-- Prove2me | Theorems.Thm_IDivGeom_ExpFam_eq_2_4
-- name    : IDivGeom.ExpFam.eq_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:19.128663+00:00
-- url     : https://prove2.me/theorems/d6125790-cee4-4b9d-9543-fde4622e0191
-- title:
--   (2.4), proof of Theorem 2.1 — a minimizing sequence in a convex set converges in variation
-- statement:
--   Let $\mathcal E$ be a convex set of probability distributions on $(X,\mathcal X)$ and $R$ a PD. Let $P_n\in\mathcal E$ be a sequence with $I(P_n\|R)<\infty$ for every $n$ and
--   $$I(P_n\|R)\to\inf_{P\in\mathcal E} I(P\|R)\qquad(2.1).$$
--   Then $P_n$ converges in variation to some PD $Q$ with $Q\ll R$:
--   $$|P_n-Q|=\int|p_{nR}-q_R|\,dR\to 0\qquad(n\to\infty).$$
--
--   This is the part of the proof of Theorem 2.1 that does not use closedness of $\mathcal E$; the limit $Q$ need not belong to $\mathcal E$. The proof of Theorem 3.3 invokes exactly this step ("$P_n$ converges in variation to some $Q$ by the proof of Theorem 2.1").
--
--   **Formalization Note** The infimum is taken in $[0,\infty]$ over the members of $\mathcal E$, all of which are PD's. The variation distance $|P_n-Q|$ is computed with $P_n+Q$ as dominating measure, which gives the same value as $R$. The page notes in parentheses that convergence in variation of $P_n\ll R$ to $Q$ implies $Q\ll R$; this is included in the conclusion.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 148 (PDF 3), (2.1) and (2.4), proof of Theorem 2.1

import Mathlib
import Definitions.Def_IDivGeom_ExpFam_Setting

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace IDivGeom.ExpFam

theorem eq_2_4 {X : Type*} [MeasurableSpace X]
    (ℰ : Set (Measure X)) (hℰ : ∀ P ∈ ℰ, IsProbabilityMeasure P) (hconv : IDivGeom.IPFP.IsConvexPD ℰ)
    (R : Measure X) [IsProbabilityMeasure R]
    (P : ℕ → Measure X) (hPℰ : ∀ n, P n ∈ ℰ) (hPfin : ∀ n, klDiv (P n) R ≠ ⊤)
    (h21 : Tendsto (fun n => klDiv (P n) R) atTop (𝓝 (⨅ P' ∈ ℰ, klDiv P' R))) :
    ∃ Q : Measure X, IsProbabilityMeasure Q ∧ Q ≪ R ∧
      Tendsto (fun n => IDivGeom.IPFP.varDist (P n) Q) atTop (𝓝 0) := by sorry

end IDivGeom.ExpFam
