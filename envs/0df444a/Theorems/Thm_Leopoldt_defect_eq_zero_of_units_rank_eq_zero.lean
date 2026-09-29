-- Prove2me | Theorems.Thm_Leopoldt_defect_eq_zero_of_units_rank_eq_zero
-- name    : Leopoldt.defect_eq_zero_of_units_rank_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-09T14:45:17.539395+00:00
-- url     : https://prove2.me/theorems/e39e37de-5933-49cb-a220-d65a0861ccd3
-- title:
--   The Leopoldt defect vanishes when Dirichlet's unit rank does
-- statement:
--   If Dirichlet's unit rank of a number field $\mathbb{K}$ vanishes, then so does its Leopoldt defect at every prime $p$:
--
--   $$\mathbb{Z}\text{-rk}\,E(\mathbb{K}) = 0 \quad \Longrightarrow \quad \mathcal{D}_L(\mathbb{K}) = 0 .$$
--
--   By Dirichlet's unit theorem $\mathbb{Z}\text{-rk}\,E(\mathbb{K}) = r_1 + r_2 - 1$, so the hypothesis holds exactly for $\mathbb{K} = \mathbb{Q}$ and for the imaginary quadratic fields; on those the conjecture is true for the trivial reason that there are no independent units to become $p$-adically dependent. It is the boundary of the conjecture's content: every other number field has $\mathbb{Z}\text{-rk}\,E(\mathbb{K}) > 0$ and the assertion $\mathcal{D}_L(\mathbb{K}) = 0$ is then a genuine constraint.
--
--   The proof is immediate from the definition, since the defect is the difference $\mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\bar{E})$ truncated in $\mathbb{N}$. The value of recording it is calibration: it pins down where the formalised defect is vacuous, and it is the base case any induction or case analysis on the unit rank starts from.
-- source:
--   Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4, 17 Feb 2016), Section 1.1 (Notations and fundamental facts), p. 3, where the defect is defined as D_L(K) = Z-rk(E) - Z_p-rk(Ebar) and it is recorded that Ebar "is a Z_p - module with Z_p-rk(Ebar) <= Z-rk(E) = r_1 + r_2 - 1". The statement below is the degenerate case Z-rk(E) = 0 of that definition. Dirichlet's unit theorem (quoted on the same page: "up to torsion made up by the roots of unity W(K), the units E = O(K)^x are a free Z-module of Z-rank r_1 + r_2 - 1") identifies the fields concerned as Q and the imaginary quadratic fields.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_eq_zero_of_units_rank_eq_zero (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] (h : Units.rank K = 0) :
    defect p K = 0 := by sorry
end Leopoldt
