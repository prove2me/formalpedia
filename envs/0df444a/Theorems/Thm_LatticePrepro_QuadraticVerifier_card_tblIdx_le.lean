-- Prove2me | Theorems.Thm_LatticePrepro_QuadraticVerifier_card_tblIdx_le
-- name    : LatticePrepro.QuadraticVerifier.card_tblIdx_le
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:38.648197+00:00
-- url     : https://prove2.me/theorems/64d5c06f-bc66-4b18-987e-a4ec13446e85
-- title:
--   Construction 4.5 — the fixed-verifier system has at most $(S+1)^2$ evaluation tables
-- statement:
--   Let $V$ be a quadratic verifier (over any $\mathbb{F}_p$) with instance length $n$ and $S$ assignment coordinates. The evaluation tables of the fixed-verifier system are indexed by
--   - the product indices: pairs $(i,j)$ with $0\le j<i\le S$, together with $(0,0)$;
--   - the auxiliary indices: $i$ with $n+1<i\le S$.
--
--   Their number $N=|\mathrm{TblIdx}|$ satisfies
--   $$N\le(S+1)^2.$$
--
--   In Construction 4.5 the paper counts $1+\binom{S+1}{2}+(S-n-1)$ evaluation tables and records the bound $(S+1)^2$. The bound is used in Theorem 4.8 to choose the moment parameter so that the hypothesis $2gN<r$ of Theorem 4.6 holds. It also bounds the number of columns.
--
--   **Formalization Note** `TblIdx` is the sum type `ProdIdx ⊕ AuxIdx` of subtypes of $\{0,\dots,S\}^2$ and $\{0,\dots,S\}$ (as `Fin (S + 1)`), and $N$ is its `Fintype.card`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Construction 4.5 (\label{con:fixed-verifier}), bound on the number of evaluation tables; Lean: LatticePrepro/Reduction/FixedSystem.lean, LatticePrepro.QuadraticVerifier.card_tblIdx_le

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

open LatticePrepro
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} (V : QuadraticVerifier p)

theorem LatticePrepro.QuadraticVerifier.card_tblIdx_le : Fintype.card V.TblIdx ≤ (V.S + 1) ^ 2 := by sorry
