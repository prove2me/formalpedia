-- Prove2me | Theorems.Thm_InfoShareH2_step1_bound
-- name    : InfoShareH2.step1_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:55.198255+00:00
-- url     : https://prove2.me/theorems/0516fb35-6c35-4ca2-9c89-b50b425273c0
-- title:
--   §9.7 Step 1 — $\sigma_I^2(QG)=S_1(Q)+\int\frac{d\mu(\lambda)}{1-\cos\lambda}\ge S_1(Q)+\mu(\mathbb T)/2$
-- statement:
--   Normalize $\sigma_\epsilon=1$. Let $\tilde\psi\in\tilde\Psi$ satisfy Assumption 2 and have no Blaschke factor: $\tilde\psi=QG$ on the disk, with $Q$ the outer part of $\tilde\psi$ and $G(z)=\exp\bigl(-\int\frac{e^{i\lambda}+z}{e^{i\lambda}-z}\,d\mu(\lambda)\bigr)$ a singular inner function with measure $\mu$. Then
--
--   $$\sigma_I^2(\tilde\psi)=S_1(Q)+c_g,\qquad c_g=\int_{-\pi}^{\pi}\frac{1}{1-\cos\lambda}\,d\mu(\lambda)\ \ge\ \frac12\mu(\mathbb T),$$
--
--   with equality in the last inequality when $\mu$ is concentrated at $\lambda=-\pi$, that is, $\mu=\gamma\,\delta_{-\pi}$.
--
--   Here $S_1(Q)=\frac1{2\pi}\int_{-\pi}^{\pi}\bigl|\frac{zQ(z)-1}{1-z}\bigr|^2d\lambda$ with $z=e^{-i\lambda}$, the outer-factor part of the inventory variance (40). The bound shows that a singular inner factor of mass $\gamma$ costs at least $\gamma/2$ in inventory variance, and this cost is smallest when the mass sits at $z=-1$.
--
--   Differences from the source:
--   - encoding: σ_ε = 1 ("Without loss of generality, we assume σ_ε = 1", §9.7) → invVar 1 ψ; reason: the normalization of §9.7
--   - reading: "we assume B(z) ≡ 1 … ψ̃(z) = Q(z)G(z)" in the proof of Theorem 2 → ψ̃ ∈ Ψ̃ with Assumption 2, ψ̃ = Q·G on D, G with constant 1 and measure µ; reason: the setting of Step 1 under the hypotheses of Theorem 2
--   - reading: "equality holds when µ concentrates at λ = −π" → if µ = γ·δ_{−π} then c_g = µ(T)/2; reason: the printed equality case
--   - encoding: σ²_I, S1(Q), ∫ 1/(1 − cos λ) dµ → σ²_I as ENNReal.ofReal; S1 and the lower integral of (1 − cos λ)⁻¹ in [0, ∞] (∞ at λ = 0); reason: a priori these quantities may be infinite
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, §9.7 Step 1, pp.41–43 (unnumbered; display after "Note that G(0) = exp(−µ(T)) and µ is symmetric", pp.42–43)

import Mathlib
import Definitions.Def_InfoShareH2_Model
import Definitions.Def_InfoShareH2_Hardy

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **§9.7 Step 1: `σ²_I(QG) = S1(Q) + c_g` and `c_g ≥ µ(T)/2`.**
SSRN 4319721 (v. 2024-01-20), §9.7 Step 1, pp.41–43 (unnumbered). With `σ_ε = 1` (§9.7, first
line) and `ψ̃ = QG` (no Blaschke factor, `B ≡ 1`), the proof writes `σ²_I = S1 + S2` with
`S1 = S1(Q)` of (40) and `S2 = c_g`, and then (pp.42–43): "`c_g = … = ∫_{−π}^{π} 1/(1 − cos λ) dµ(λ)
≥ (1/2)µ(T)`, where equality holds when `µ` concentrates at `λ = −π`."

**Formalization Note** Stated for `ψ̃ ∈ Ψ̃` satisfying Assumption 2 (the hypotheses of Theorem 2, under
which §9.7 uses Lemma 6) whose factorization of Lemma 2 has `B ≡ 1`: `ψ̃ = Q·G` on `D` with `Q` the
outer part and `G` a singular inner function with constant `1` and measure `µ`. The integral
`∫ 1/(1 − cos λ) dµ` is a lower integral in `ℝ≥0∞` (`1/0 = ∞` at `λ = 0`); `S1(Q)` is in `ℝ≥0∞` as
well, and `σ²_I(ψ̃) = invVar 1 ψ̃` is finite on `Ψ̃`. -/
theorem step1_bound (ψ : ℕ → ℝ) (hψ : ψ ∈ PsiTilde) (hA2 : Assumption2 ψ)
    (G : SingularData) (hG : G.c = 1)
    (hfac : ∀ z ∈ Disk, zTransform (ofRealSeq ψ) z = outerPart (ofRealSeq ψ) z * G.eval z) :
    ENNReal.ofReal (invVar 1 ψ) =
        S1 (outerPart (ofRealSeq ψ)) + ∫⁻ lam, (ENNReal.ofReal (1 - Real.cos lam))⁻¹ ∂G.μ ∧
    G.μ Set.univ / 2 ≤ ∫⁻ lam, (ENNReal.ofReal (1 - Real.cos lam))⁻¹ ∂G.μ ∧
    ∀ γ : ENNReal, G.μ = γ • Measure.dirac (-Real.pi) →
      ∫⁻ lam, (ENNReal.ofReal (1 - Real.cos lam))⁻¹ ∂G.μ = G.μ Set.univ / 2 := by sorry

end InfoShareH2
