-- Prove2me | Theorems.Thm_HawkesParking_Spine_borel_law
-- name    : HawkesParking.Spine.borel_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:24.285768+00:00
-- url     : https://prove2.me/theorems/11aae497-3c73-4d6b-8440-c2127296fb38
-- title:
--   Eq. (4), p. 7 — the cluster size is Borel$(\rho)$: $P(N=k+1)=e^{-\rho(k+1)}(\rho(k+1))^k/(k+1)!$
-- statement:
--   Let $g$ be an excitation kernel satisfying the standing assumptions, with $\rho=\int_0^\infty g$. For every $k\in\mathbb N$, the total mass of the size-$(k+1)$ cluster law is the Borel$(\rho)$ probability of $k+1$:
--   $$P(N=k+1)=\frac{e^{-\rho(k+1)}}{(k+1)!}\big(\rho(k+1)\big)^{k}.$$
--
--   The cluster is a Poisson($\rho$) branching process, so its total progeny is Borel distributed; this is the normalizing constant of Lemma 2.
--
--   **Formalization Note.** The paper states $P(N=k)=e^{-\rho k}(\rho k)^{k-1}/k!$ for $k\in\mathbb Z_+$; it is indexed here by $k+1$ with $k\in\mathbb N$, which is the same family and avoids the natural-number subtraction $k-1$ at $k=0$. Here $P(N=k+1)$ is the total mass of the likelihood-defined cluster law (see the Model item), so the statement also checks that this law is the paper's.
-- source:
--   Daw, Conditional Uniformity and Hawkes Processes, arXiv:2202.05335v2, p. 7, eq. (4)

import Mathlib
import Definitions.Def_HawkesParking_Spine_Model

namespace HawkesParking.Spine
open MeasureTheory
theorem borel_law (g : ℝ → ℝ) (hg : IsKernel g) (k : ℕ) :
    clusterLaw g k Set.univ =
      ENNReal.ofReal (Real.exp (-(rho g * (k + 1))) / ((k + 1).factorial : ℝ) *
        (rho g * (k + 1)) ^ k) := by sorry
end HawkesParking.Spine
