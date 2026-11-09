-- Prove2me | Theorems.Thm_GroupIsoPoly_corollary_4_2
-- name    : GroupIsoPoly.corollary_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:55:58.630362+00:00
-- url     : https://prove2.me/theorems/27633ee1-2dba-4130-a54c-cf63b9b32e13
-- title:
--   Corollary 4.2 — quadratic form tuple isometry over $\mathbb F_{2^f}$ in time $2^{O(fn)}\cdot\mathrm{poly}(n,m)$
-- statement:
--   There are a deterministic algorithm and a constant $C$ such that for every finite field $\mathbb F_{2^e}$ (given by a presentation), all $n,m$ and all tuples $(f_1,\dots,f_m)$, $(g_1,\dots,g_m)$ of quadratic forms (homogeneous quadratic polynomials) in $\mathbb F_{2^e}[x_1,\dots,x_n]$, the algorithm decides whether the tuples are isometric — whether some $A\in\mathrm{GL}(n,2^e)$ has $f_i=g_i\circ A$ for all $i$, with $(g\circ A)(x)=g(\sum_ja_{1,j}x_j,\dots,\sum_ja_{n,j}x_j)$ — within
--   $$
--   C\cdot2^{\,C\,e\,\max(n,1)}\cdot(n+m+2)^C
--   $$
--   steps.
--
--   In characteristic 2 quadratic forms are not determined by their bilinear forms, so isometry is a separate problem from congruence; with $e=1$ (and Theorem 4.1) this is Theorem 1.3.
--
--   **Formalization Note** Forms are given by their $n(n+1)/2$ coefficients (`encQFTI`).
--
--   Differences from the source:
--
--   - reading: 2^O(fn) · poly(n, m)-time → C · 2^(C·e·max(n,1)) · (n+m+2)^C steps of one machine, C chosen before the field and the dimensions; reason: for n ≥ 1 this is the printed bound; at n = 0 the printed bound poly(m) does not cover reading the field description (Θ(e) bits), which every machine must read
--   - encoding: quadratic forms over F_{2^f} → a presented field `P : FieldPres` with `P.p = 2`, exponent e = deg of the defining polynomial, in the input with coefficients in power-basis coordinates; reason: an algorithm over every F_{2^f} needs the field in its input; every finite field has a presentation; the paper's letter f is renamed e because `P.f` is the polynomial
--   - encoding: "quadratic forms (homogeneous quadratic polynomials)" → `MvPolynomial (Fin n) F` with `IsHomogeneous 2` as hypotheses, coded by the coefficients of x_i x_j, i ≤ j; reason: the standard representation; the code is injective on quadratic forms
--   - reading: isometric, Definition 11 (p.27), printed as (g∘A)(x) = g(Σ_j a_{1,j}x_j, …, Σ_j a_{n,j}x_n) → (g∘A)(x) = g(Σ_j a_{1,j}x_j, …, Σ_j a_{n,j}x_j); reason: Definition 11 and Definition 2 (p.2) both print x_n in the last slot against x_j in the first; with x_n the last argument would be (Σ_j a_{n,j})·x_n and g∘A would not be the substitution by A, so x_j is the evident intent
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Corollary 4.2, p.27 (PDF p.31); Definition 11, p.27

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_GroupIsoPoly_QFIsometric
import Definitions.Def_GroupIsoPoly_encQFTI

set_option autoImplicit false

namespace GroupIsoPoly

open AvgCaseTI (FieldPres)

open Classical in
/-- **Corollary 4.2 (Quadratic-form tuple isometry algorithm over `F_{2^f}`).**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Corollary 4.2, p.27 (PDF p.31): "Let (f1, . . . , fm),
(g1, . . . , gm) ∈ F_{2^f}[x1, . . . , xn]^m be two tuples of quadratic forms. There is a
2^O(fn) · poly(n, m)-time algorithm that decides whether the two tuples are isometric."

There are one deterministic machine `M` and one constant `C` such that for every presented field
`F_{2^e}`, all `n, m` and all tuples `f, g` of quadratic forms (homogeneous of degree 2) in `n`
variables, `M` on the code of `(n, m, F, f, g)` halts within `C · 2^(C·e·max(n,1)) · (n + m + 2)^C`
steps with output `1` if the tuples are isometric (Definition 11) and `0` otherwise.

**Formalization Note.** As in `theorem_4_1`; forms are coded by their `n(n+1)/2` coefficients. -/
theorem corollary_4_2 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ P : FieldPres, P.p = 2 →
      ∀ (n m : ℕ) (f g : Fin m → MvPolynomial (Fin n) P.F),
        (∀ i, (f i).IsHomogeneous 2) → (∀ i, (g i).IsHomogeneous 2) →
        HMBinPacking.OutputsWithin M (encQFTI P n m f g) [decide (QFIsometric f g)]
          (C * 2 ^ (C * P.f.natDegree * max n 1) * (n + m + 2) ^ C) := by sorry

end GroupIsoPoly
