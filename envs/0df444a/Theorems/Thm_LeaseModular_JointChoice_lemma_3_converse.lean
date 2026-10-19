-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_lemma_3_converse
-- name    : LeaseModular.JointChoice.lemma_3_converse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:28.911358+00:00
-- url     : https://prove2.me/theorems/87a5b66b-efe0-4f9f-8941-50aa32ff278f
-- title:
--   Proof of Lemma 3 and Proposition 2, p. 36 — for γ < 1, selling beats leasing under architecture j iff c > C_j
-- statement:
--   Throughout, $\delta_1,\delta_2$ are the module durabilities under selling, $\gamma>0$ the relative return condition of off-lease modules (durabilities under leasing $\delta_{kl}=\gamma\delta_k$), and $c$ the per-module production cost, subject to the standing assumptions $0<\delta_2<\delta_1<1$, $\gamma\delta_1<1$, $0<c<(1-\delta_2)/2$ and $c<(1-\gamma\delta_2)/2$.
--
--   Suppose in addition $\gamma<1$ (off-lease products depreciate more than previously sold ones). Then the optimal profits exist and
--
--   1. $\Pi^*_{LI}<\Pi^*_{SI}$ if and only if $c>C_I(\delta_1,\delta_2,\gamma)$;
--   2. $\Pi^*_{LM}<\Pi^*_{SM}$ if and only if $c>C_M(\delta_1,\delta_2,\gamma)$;
--   3. $C_I<C_{LI}$ and $C_M<C_{LM1}$.
--
--   Together with Lemma 3, this characterizes the lease-versus-sell choice under each architecture by a single cost threshold.
--
--   **Formalization Note.** The paper's summary sentence reads "if and only if $\gamma>1$ and $c>C_j$"; the proof treats the case $\gamma<1$ (for $\gamma\ge1$ leasing is never worse), so the statement is made for $\gamma<1$. At $\gamma=1$ the comparisons are ties above the threshold, which is why $\gamma=1$ is excluded.
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), proof of Lemma 3 and Proposition 2, Appendix p. 36

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Proof of Lemma 3 and Proposition 2, p. 36. For `γ < 1`: selling an integral product is
strictly more profitable than leasing it iff `c > C_I(δ₁, δ₂, γ)`, selling a modular product is
strictly more profitable than leasing it iff `c > C_M(δ₁, δ₂, γ)`, and `C_I < C_LI`,
`C_M < C_LM1`. -/
theorem lemma_3_converse (P : Params) (hP : Standing P) (hγ : P.γ < 1) :
    ∃ vSI vLI vSM vLM : ℝ, IsOptSI P vSI ∧ IsOptLI P vLI ∧ IsOptSM P vSM ∧ IsOptLM P vLM ∧
      (vLI < vSI ↔ CI P.δ₁ P.δ₂ P.γ < P.c) ∧
      (vLM < vSM ↔ CM P.δ₁ P.δ₂ P.γ < P.c) ∧
      CI P.δ₁ P.δ₂ P.γ < CLI P.δ₁ P.δ₂ P.γ ∧ CM P.δ₁ P.δ₂ P.γ < CLM1 P.δ₁ P.γ := by sorry

end LeaseModular.JointChoice
