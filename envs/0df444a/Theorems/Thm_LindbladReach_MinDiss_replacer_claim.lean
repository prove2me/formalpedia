-- Prove2me | Theorems.Thm_LindbladReach_MinDiss_replacer_claim
-- name    : LindbladReach.MinDiss.replacer_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:37.479856+00:00
-- url     : https://prove2.me/theorems/dd35201a-6979-45f5-8d1b-6a278501afd2
-- title:
--   Proof of Theorem 2.12, p. 8 — R_{|0⟩⟨0|} ⊗ id = lim e^{tL_a}, and R_{|0⟩⟨0|} ⊗ id and R_{|0_k⟩⟨0_k|} are in the closed class Channel(S)
-- statement:
--   Let $H=\mathbb C^{2^k}$ with $k\ge1$, and let $S=S^*$ generate a Hörmander system with $a=|0\rangle\langle1|\otimes I^{\otimes(k-1)}\in S$. Write $\mathcal R_\sigma(\rho)=\operatorname{tr}(\rho)\,\sigma$ for the replacer channel. Then:
--
--   1. the amplitude-damping semigroup of $a$ converges to the reset of the first qubit,
--   $$\lim_{t\to\infty}e^{tL_a}=\mathcal R_{|0\rangle\langle0|}\otimes\mathrm{id},\qquad (\mathcal R_{|0\rangle\langle0|}\otimes\mathrm{id})(\rho)=|0\rangle\langle0|\otimes\operatorname{tr}_1\rho;$$
--   2. $\mathcal R_{|0\rangle\langle0|}\otimes\mathrm{id}\in\overline{\mathrm{Channel}(S)}$;
--   3. $\mathcal R_{|0_k\rangle\langle0_k|}\in\overline{\mathrm{Channel}(S)}$, where $\mathcal R_{|0_k\rangle\langle0_k|}(\rho)=\operatorname{tr}(\rho)\,|0_k\rangle\langle0_k|$.
--
--   This is the first half of the proof of Theorem 2.12: all information in a state can be erased to the reference state $|0_k\rangle$.
--
--   **Formalization Note** $k\ge1$ is added because the page names the first qubit. The page's "by assumption" is posed as a claim. The hypothesis $Z_1\in S$ of Theorem 2.12 is not used for this step and is omitted. Limits are in the operator-norm topology of superoperators.
-- source:
--   Cai, Govindarajan, Junge, How Far do Lindbladians Go?, arXiv:2504.04883v2, p. 8, proof of Theorem 2.12; replacer channel R_σ defined on p. 4

import Mathlib
import Definitions.Def_LindbladReach_MinDiss_Setting

namespace LindbladReach.MinDiss

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

/-- Proof of Theorem 2.12, p. 8: `R_{|0⟩⟨0|} ⊗ id = lim_{t→∞} e^{tL_a}` for `a = |0⟩⟨1| ⊗ I^{⊗(k−1)}`,
and `R_{|0⟩⟨0|} ⊗ id` and `R_{|0_k⟩⟨0_k|}` lie in the closed class. -/
theorem replacer_claim {k : ℕ} (hk : 0 < k) (S : Set (Mat k)) (hS : ∀ a ∈ S, aᴴ ∈ S)
    (hH : IsHormander S) (ha : ampDamp ⟨0, hk⟩ ∈ S) :
    Filter.Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • dissipator (ampDamp ⟨0, hk⟩)))
        Filter.atTop (nhds (resetQubit ⟨0, hk⟩)) ∧
      resetQubit ⟨0, hk⟩ ∈ channelClosure S ∧ resetAll k ∈ channelClosure S := by sorry

end LindbladReach.MinDiss
