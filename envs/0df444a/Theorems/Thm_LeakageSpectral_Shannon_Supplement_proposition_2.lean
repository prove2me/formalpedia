-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_proposition_2
-- name    : LeakageSpectral.Shannon.Supplement.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:45:45.468761+00:00
-- url     : https://prove2.me/theorems/99bb16d1-ada7-42f7-9c98-92a42d91acf9
-- title:
--   Proposition 2, p. 21 — finite-share perfect leakage cancellation on $\mathbb Z_5$
-- statement:
--   Let $\mathbb G=\mathbb Z_5$ with the discrete $\sigma$-algebra, $\varphi_0=\mathrm{id}$ and $\varphi_1(s)=2s$, and consider the **automorphism-weighted sharing** $Z=\varphi_0(S_0)+\varphi_1(S_1)=S_0+2S_1$ with independent uniform shares $S_0,S_1$ and leakage $X=(L_0,L_1)$, $L_i\sim\tau(S_i)$.
--
--   There is a full-support binary leakage channel $\tau$ (a Markov kernel from $\mathbb Z_5$ to $\{0,1\}$ with every transition probability positive), non-trivial in the sense $I(S;L)>0$, such that, using $\tau$ for both shares,
--   $$I(Z;X)=0,$$
--   with $I$ the Shannon mutual information in bits.
--
--   It shows that automorphism weights can cancel the global leakage completely with finitely many shares, which never happens for unweighted sharing with i.i.d. non-trivial leakage (Theorem 11).
--
--   Differences from the source:
--
--   - encoding: φ₀ = id, φ₁(S₁) = 2S₁ → the conclusion for every φ : Fin 2 → (ZMod 5 ≃+ ZMod 5) with φ 0 s = s and φ 1 s = 2 * s; reason: such an automorphism exists and is unique (2 is a unit mod 5; existence checked in the mission's verification module), so the clause is about that φ and is not vacuous
--   - reading: "Full-support leakage channels exist such that I(Z;X) = 0" → one full-support Markov kernel τ : Kernel (ZMod 5) Bool, with 0 < shannonMI (localJoint τ), used for both shares; reason: the proof's channel (11) is binary and is used for both shares; I(S;L) > 0 is the standing assumption of §2.1 and makes the example non-trivial
--   - encoding: the law of (Z, X) for automorphism-weighted sharing (§5.3) → weightedGlobalJoint, m^{−(d+1)} Σ_s δ_{Σ φ_i(s_i)} ⊗ ⊗_i τ(s_i); reason: every quantity depends only on this law; with all φ_i the identity it is the base globalJoint (verification module)
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Proposition 2, p. 21; channel Eq. (11)

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Proposition 2, p. 21: finite-share perfect leakage cancellation.
For `G = ℤ₅`, `φ₀ = id`, `φ₁(s) = 2s` and the automorphism-weighted sharing `Z = S₀ + 2 S₁`, there is a
full-support binary channel `τ`, non-trivial (`I(S; L) > 0`), used for both shares, with
`I(Z; X) = 0`. -/
theorem proposition_2 :
    ∃ τ : Kernel (ZMod 5) Bool, IsMarkovKernel τ ∧ FullSupport τ ∧ 0 < shannonMI (localJoint τ) ∧
      ∀ φ : Fin 2 → (ZMod 5 ≃+ ZMod 5), (∀ s, φ 0 s = s) → (∀ s, φ 1 s = 2 * s) →
        shannonMI (weightedGlobalJoint (fun _ : ℕ => τ) φ) = 0 := by sorry

end LeakageSpectral.Shannon.Supplement
