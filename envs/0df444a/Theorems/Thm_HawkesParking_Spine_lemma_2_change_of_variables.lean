-- Prove2me | Theorems.Thm_HawkesParking_Spine_lemma_2_change_of_variables
-- name    : HawkesParking.Spine.lemma_2_change_of_variables
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:33.797491+00:00
-- url     : https://prove2.me/theorems/3abfe0dc-ed4b-4f7a-80e8-bafe88cd1086
-- title:
--   Proof of Lemma 2, p. 11 — the joint density of $(\Lambda_1,\dots,\Lambda_k)$ and $\{N=k+1\}$ is $e^{-(k+1)\rho}$ on $\mathcal P_k$
-- statement:
--   Let $g$ be an excitation kernel satisfying the standing assumptions, with $\rho=\int_0^\infty g$, and let $k\in\mathbb N$. Push the size-$(k+1)$ cluster law $P(N=k+1,(A_1,\dots,A_k)\in\cdot)$ forward by the compensator map $(A_1,\dots,A_k)\mapsto(\Lambda_1,\dots,\Lambda_k)$, $\Lambda_j=\sum_{i=0}^{j-1}G(A_j-A_i)$. The result has constant density $e^{-(k+1)\rho}$ on the polytope $\mathcal P_k$:
--   $$P\big(N=k+1,\ (\Lambda_1,\dots,\Lambda_k)\in dx\big)=e^{-(k+1)\rho}\,\mathbf 1_{\mathcal P_k}(x)\,dx .$$
--
--   This is the identity $P(N=k+1\mid\Lambda_1,\dots,\Lambda_k)\,e^{-\Lambda_k}=e^{-(k+1)\rho}$ of the proof of Lemma 2, combined with the unconditioned density $e^{-\Lambda_k}$ of the compensator points. It does not depend on $g$ beyond $\rho$.
--
--   **Formalization Note.** The statement is taken from the proof of Lemma 2, not from a numbered result. It is stated as an equality of measures on $\mathbb R^k$ in compensator coordinates, starting from the likelihood definition of the cluster law (see the Model item).
-- source:
--   Daw, Conditional Uniformity and Hawkes Processes, arXiv:2202.05335v2, pp. 10–11, proof of Lemma 2

import Mathlib
import Definitions.Def_HawkesParking_Spine_Model

namespace HawkesParking.Spine
open MeasureTheory
theorem lemma_2_change_of_variables (g : ℝ → ℝ) (hg : IsKernel g) (k : ℕ) :
    (clusterLaw g k).map (compensator g) =
      ENNReal.ofReal (Real.exp (-((k + 1 : ℝ) * rho g))) •
        volume.restrict (polytope k (rho g)) := by sorry
end HawkesParking.Spine
