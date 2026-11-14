-- Prove2me | Theorems.Thm_LatticePrepro_exists_explicit_momentRepresentation
-- name    : LatticePrepro.exists_explicit_momentRepresentation
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:26:03.500822+00:00
-- url     : https://prove2.me/theorems/85edd36b-2212-4060-ac2c-3f728d9423f5
-- title:
--   Theorem A.8 — explicit moment representations
-- statement:
--   Let $p$ be a prime and let $S,m,B$ be integers with $S\ge2$, $m\ge1$ and $B\ge2$. Then there exists an explicit moment representation with these parameters. That is, there are
--
--   - a field $K$ of characteristic $p$ (an $\mathbb{F}_p$-algebra),
--   - elements $E_1,\dots,E_S\in K$ that are linearly independent over $\mathbb{F}_p$ (together with $E_0=0$),
--   - a natural number $q$ with
--     $$q=p^d\ \text{for some } d\ge1,\qquad B\le q<8\,p^3\,m\,S\,B,$$
--   - and a moment representation over $K$ (Definition 4.4) with moment parameter $r=B^m$ and $q$ blocks of size $q^m$: evaluation tables $y\in\mathbb{F}_p^{\iota}$ on a finite coordinate set $\iota$ partitioned into the blocks, an $\mathbb{F}_p$-linear constraint map $C$, and $\mathbb{F}_p$-linear moment maps $\hat\mu_0,\dots,\hat\mu_{2r-2}\colon\mathbb{F}_p^{\iota}\to K$,
--
--   such that the following hold.
--
--   1. **Completeness.** For every $\alpha\in K$ there is a binary table $y$ with exactly one nonzero coordinate in each block, $C(y)=0$, and $\hat\mu_k(y)=\alpha^k$ for $0\le k\le2r-2$.
--   2. **Soundness.** For every $y\in\mathbb{F}_p^{\iota}$ with $C(y)=0$ and $2\,\mathrm{wt}(y)<r\,q$, there is a finitely supported coefficient function $f\colon\overline{K}\to\mathbb{F}_p$ on an algebraic closure $\overline{K}$ of $K$ such that
--      $$\hat\mu_k(y)=\mu_k(f)=\sum_{\alpha\in\overline{K}}f(\alpha)\,\alpha^k\quad(0\le k\le2r-2),\qquad q\cdot|\mathrm{supp}\,f|\le2\,\mathrm{wt}(y).$$
--
--   Here $\mathrm{wt}(y)$ is the number of nonzero coordinates of $y$.
--
--   The paper proves these properties for the concrete output of Construction A.4: $K=\mathbb{S}(\gamma)$ of degree $\delta$ (the least power of $p$ that is at least $S$) over a sample field $\mathbb{S}$ of size $q$ (the least power of $p$ that is at least $8pmB\delta$), the encoding tuple $(1,\gamma,\dots,\gamma^{S-1})$, and the polynomial evaluation tables. Theorem 4.8 uses this representation to instantiate the fixed-verifier reduction (Construction 4.5, Theorem 4.6) with the stated size bounds.
--
--   **Formalization Note**: The statement is `Nonempty (ExplicitMomentRepresentation p S m B)`, a structure bundling the field, the encoding tuple (indexed by `Fin (S + 1)` with $E_0=0$), the moment representation and $q$ with the equations above. It is an existence statement: the concrete construction, the finiteness of $K$ and the construction-time part (item 3 of Theorem A.8) are not part of it. Coefficient functions have type `AlgebraicClosure K →₀ ZMod p`, so all represented functions live on one fixed extension rather than on a finite extension depending on $y$. The constraint matrix is an $\mathbb{F}_p$-linear map, and moment orders are indexed by `Fin (2r - 1)`. The paper writes $\kappa,\tau,N,\mathbb{E},\mathsf d,\mathsf a$ for $r,q,S,K,B,m$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem A.8 (\label{thm:moment-representation-construction}); Lean: LatticePrepro/Tables/Explicit.lean, LatticePrepro.exists_explicit_momentRepresentation

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit

open LatticePrepro
open Polynomial
open ExplicitTables

theorem LatticePrepro.exists_explicit_momentRepresentation (p : ℕ) [Fact p.Prime] (S m B : ℕ)
    (hS : 2 ≤ S) (hm : 1 ≤ m) (hB : 2 ≤ B) : Nonempty (ExplicitMomentRepresentation p S m B) := by sorry
