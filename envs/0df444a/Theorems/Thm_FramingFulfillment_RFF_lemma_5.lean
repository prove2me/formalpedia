-- Prove2me | Theorems.Thm_FramingFulfillment_RFF_lemma_5
-- name    : FramingFulfillment.RFF.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:37.596115+00:00
-- url     : https://prove2.me/theorems/cc175f38-e041-485f-9a9a-6a3c2eb33b3f
-- title:
--   Lemma 5, p. 22 — 𝒥* ≤ 𝒥^D: the deterministic program DET' bounds the optimal expected profit
-- statement:
--   For a JFF instance satisfying the standing assumptions, the optimal expected profit $\mathcal J^*$ of the stochastic control problem OPT' is at most the optimal value $\mathcal J^D$ of the deterministic program DET':
--
--   $$\mathcal J^*\le\mathcal J^D.$$
--
--   This is the upper bound against which the RFF policy is measured in Theorem 2.
--
--   **Formalization Note** $\mathcal J^*$ is the value of the Bellman recursion of OPT': framings that hide every out-of-stock product and fulfillment from an FC with stock. $\mathcal J^D$ is the supremum of the DET' objective over its feasible set.
-- source:
--   Lei, Jasin, Uichanco & Vakhutinsky, Joint Product Framing and Order Fulfillment under the MNL Model, SSRN 3282019 (PDF sha256 7d6bd797…), p. 22, Lemma 5 (proof: Electronic Companion EC 1, EC pp. 1–2, PDF 34–35)

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

namespace FramingFulfillment.RFF

/-- Lemma 5 (p. 22): `𝒥* ≤ 𝒥^D`. -/
theorem lemma_5 (P : Inst) (hP : P.Standing) : P.Jstar ≤ P.JD := by sorry

end FramingFulfillment.RFF
