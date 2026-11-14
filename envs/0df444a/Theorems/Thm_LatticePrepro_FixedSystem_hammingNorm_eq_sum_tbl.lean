-- Prove2me | Theorems.Thm_LatticePrepro_FixedSystem_hammingNorm_eq_sum_tbl
-- name    : LatticePrepro.FixedSystem.hammingNorm_eq_sum_tbl
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:34.549653+00:00
-- url     : https://prove2.me/theorems/241a4974-8345-47a7-a959-240859c1c548
-- title:
--   Weight of a fixed-system vector is the sum of the weights of its tables
-- statement:
--   Consider the fixed-verifier system of Construction 4.5 for a quadratic verifier $V$ over $\mathbb{F}_p$ ($p$ prime) and a moment representation $R$ over a field $K\supseteq\mathbb{F}_p$, with table coordinates $\iota$. Its columns are the pairs $(T,i)$ of a table index $T\in\mathrm{TblIdx}$ and a coordinate $i\in\iota$. For every $v\in\mathbb{F}_p^{\mathrm{TblIdx}\times\iota}$,
--   $$\operatorname{wt}(v)=\sum_{T\in\mathrm{TblIdx}}\operatorname{wt}(v_T),$$
--   where $v_T=(v_{(T,i)})_{i\in\iota}\in\mathbb{F}_p^\iota$ is the table with index $T$, and $\operatorname{wt}$ is the Hamming weight (the number of nonzero coordinates).
--
--   This bookkeeping identity is used in the soundness part of Theorem 4.6. It bounds the weight of each table by the total weight and lets the per-table support bounds of the moment representation be summed.
--
--   **Formalization Note** The Hamming weight is Mathlib's `hammingNorm`, and $v_T$ is `tbl V R v T`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847); auxiliary lemma used in the proof of Theorem 4.6 (\label{thm:fixed-verifier-reduction}); Lean: LatticePrepro/Reduction/FixedSystem.lean, LatticePrepro.FixedSystem.hammingNorm_eq_sum_tbl

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)
open LatticePrepro.FixedSystem

theorem LatticePrepro.FixedSystem.hammingNorm_eq_sum_tbl (v : Col V R → ZMod p) :
    hammingNorm v = ∑ T, hammingNorm (tbl V R v T) := by sorry
