-- Prove2me | Theorems.Thm_HasseHSG_Generator_theorem_1_2
-- name    : HasseHSG.Generator.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:53.94294+00:00
-- url     : https://prove2.me/theorems/4d87c9bd-63ea-4751-b2a8-7935de1407a3
-- title:
--   Theorem 1.2 — an explicit bivariate hitting set generator of degrees $O(nr^2d)$ in $t$ and $O(nr^3d)$ in $z$ for polynomials with small Hasse derivative space
-- statement:
--   Let $n,r,d$ be nonnegative integers and $F$ a field with $|F|\ge2n^2r^4d^2$ (of any characteristic, finite or infinite). Then there is an **explicit** polynomial map
--   $$G:F\times F\to F^n,\qquad (z,t)\mapsto(G_1(z,t),\dots,G_n(z,t)),$$
--   with $\deg_tG_i=O(nr^2d)$ and $\deg_zG_i=O(nr^3d)$, such that for every $f\in F[x_1,\dots,x_n]$ of total degree at most $d$ with $\dim_F\hat\partial^*f\le r$,
--
--   $$f(x_1,\dots,x_n)\neq0\iff f(G_1,\dots,G_n)\neq0\quad\text{in }F[z,t].$$
--
--   Here $\hat\partial^*f$ is the span of all Hasse derivatives of $f$. "Explicit" means that $G$ can be constructed in time $\mathrm{poly}(n,r,d)$ (Remark 1.3).
--
--   The Lean statement makes every quantifier explicit. There are one program $P$ of the uniform algebraic machine `EllipticRootFinding.Online` and constants $C,k\in\mathbb N$, all fixed before the field and the parameters, such that the following holds for every field $F$, all $n,r,d$, and every list $e$ of $2n^2r^4d^2$ pairwise distinct elements of $F$. Such a list exists exactly when $|F|\ge 2n^2r^4d^2$.
--
--   1. **Halting and time.** $P$ on input $(n,r,d,e)$ halts after at most $C(n+r+d+2)^k$ executed instructions.
--   2. **Word size.** Every integer register stays bounded by $C(n+r+d+2)^k$ in absolute value throughout the run.
--   3. **Output.** The output lists $G_1,\dots,G_n\in F[z,t]$, with
--   $$\deg_tG_i\le C\,n\,r^2d,\qquad \deg_zG_i\le C\,n\,r^3d.$$
--   4. **Hitting property.** $G$ is a hitting set generator for the class $\{f:\deg f\le d,\ \dim\hat\partial^*f\le r\}$.
--
--   This is the first construction of this kind over fields of arbitrary characteristic. Since polynomials computed by depth-3 powering circuits have small Hasse derivative space, it yields polynomial-size hitting sets for that class over every field (Corollary 1.4).
--
--   **Formalization Note.** $F$ ranges over `Type` (the machine's universe). $G_i$ is an `MvPolynomial (Fin 2) F` with $z$ = `X 0` and $t$ = `X 1`. $f(G)$ is `aeval G f`, a polynomial identity rather than evaluation at points of $F^2$. $\dim$ is `Module.rank` (a cardinal).
--
--   Differences from the source:
--   - reading: 'explicit': G can be constructed in time poly(n, r, d) (Remark 1.3) → one program P of the uniform algebraic machine EllipticRootFinding.Online and constants C, k fixed before F, n, r, d; P halts within C(n+r+d+2)^k executed instructions with every integer register bounded by C(n+r+d+2)^k in absolute value; reason: the remark does not fix a model; a field-uniform machine with total-step time and polynomial word size is the standard reading over an arbitrary field
--   - encoding: |F| ≥ 2n²r⁴d² → the program receives a duplicate-free list e of exactly 2n²r⁴d² elements of F; reason: such a list exists exactly when |F| ≥ 2n²r⁴d² as cardinals, so every field the source covers is covered; the list is how an algorithm with constants 0, 1 accesses field elements
--   - encoding: deg_t G_i = O(nr²d), deg_z G_i = O(nr³d) → degreeOf t (G i) ≤ C·n·r²·d and degreeOf z (G i) ≤ C·n·r³·d with the same universal C; reason: O(·) with a universal constant and no additive term (true also at nd = 0, INSIGHTS I1)
--   - encoding: a field F → F : Type (universe 0); reason: the published machine's state type lives in Type
--   - encoding: dim ∂̂*f ≤ r; f(G) ≠ 0 → Module.rank F (hasseSpace f) ≤ r; aeval G f ≠ 0 in MvPolynomial (Fin 2) F; reason: cardinal dimension; f(G) ≠ 0 as a polynomial (the paper's polynomial view)
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), pp. 5–6, Theorem 1.2 and Remark 1.3; proof p. 38 (§8, Eqs. (19)–(22))

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine
import Definitions.Def_HasseHSG_Generator_HasseSpace
import Definitions.Def_HasseHSG_Generator_Explicit

open EllipticRootFinding.Online

namespace HasseHSG.Generator

/-- Theorem 1.2 (pp. 5–6) with Remark 1.3 ("explicit" = constructible in time poly(n, r, d)).
One program `P` and constants `C, k`, fixed before everything else: for every field `F`, all
`n, r, d` and every duplicate-free list `e` of `2n²r⁴d²` elements of `F` (such a list exists
exactly when `|F| ≥ 2n²r⁴d²`), `P` on input `(n, r, d, e)` halts within `C (n+r+d+2)^k` steps with
every integer register bounded by `C (n+r+d+2)^k` throughout, and outputs `G₁, …, Gₙ ∈ F[z, t]`
(`z = X 0`, `t = X 1`) with `deg_t Gᵢ ≤ C n r² d`, `deg_z Gᵢ ≤ C n r³ d`, which is a hitting set
generator for all `f ∈ F[x₁, …, xₙ]` of total degree `≤ d` with `dim ∂̂* f ≤ r`. -/
theorem theorem_1_2 :
    ∃ (P : Program) (C k : ℕ), ∀ (F : Type) [Field F] (n r d : ℕ) (e : List F),
      e.Nodup → e.length = 2 * n ^ 2 * r ^ 4 * d ^ 2 →
      ∃ T : ℕ,
        ((exec P T (initState (generatorInput n r d e))).1.instr P).isHalt = true ∧
        T ≤ C * (n + r + d + 2) ^ k ∧
        (∀ t ≤ T, ∀ j : ℕ,
          |(exec P t (initState (generatorInput n r d e))).1.ir j| ≤
            ((C * (n + r + d + 2) ^ k : ℕ) : ℤ)) ∧
        ∃ out : Val F,
          out.ints = outInts (exec P T (initState (generatorInput n r d e))).1 ∧
          out.flds = outFlds (exec P T (initState (generatorInput n r d e))).1 ∧
          ∃ G : Fin n → MvPolynomial (Fin 2) F, IsGeneratorVal out G ∧
            (∀ i, (G i).degreeOf 1 ≤ C * n * r ^ 2 * d ∧ (G i).degreeOf 0 ≤ C * n * r ^ 3 * d) ∧
            IsHittingSetGenerator G (hasseClass F n d r) := by sorry

end HasseHSG.Generator
