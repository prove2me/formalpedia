-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_Supplement_theorem_11
-- name    : LeakageSpectral.Shannon.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:16.784277+00:00
-- url     : https://prove2.me/theorems/4670bc40-aed3-4cd1-b47a-685ad7327bdb
-- title:
--   Theorem 11, p. 21 — spectral de-alignment and finite-share perfect leakage cancellation
-- statement:
--   For a finite abelian group $\mathbb G$ (discrete $\sigma$-algebra), a leakage channel $\tau$ with Fourier power spectrum $\lambda(w)=\mathbb E_L|\hat p_{S\mid L}(w\mid L)|^2$, and automorphisms $\varphi_0,\dots,\varphi_d$ of $\mathbb G$, consider the **automorphism-weighted sharing** $Z=\sum_{i=0}^d\varphi_i(S_i)$ with independent uniform shares and leakage $X=(L_0,\dots,L_d)$, $L_i\sim\tau(S_i)$. Write $A_i^*w=w\circ\varphi_i$ for the action of $\varphi_i$ on characters (Eq. (9)) and $\operatorname{supp}\lambda=\{w\ne0:\lambda(w)\ne0\}$.
--
--   1. For every finite abelian $\mathbb G$, every non-trivial channel $\tau$ ($I(S;L)>0$), every $d$ and all automorphisms $\varphi_0,\dots,\varphi_d$:
--   $$I(Z;X)=0\iff\bigcap_{i=0}^{d}(A_i^*)^{-1}(\operatorname{supp}\lambda)=\emptyset,$$
--   i.e. iff there is no non-trivial character $w$ with $\lambda(w\circ\varphi_i)\ne0$ for every $i$.
--   2. The condition is achievable with finitely many shares: on $\mathbb G=\mathbb Z_5$ there are a full-support binary non-trivial channel $\tau$ and automorphisms $\varphi_0,\varphi_1$ with $I(Z;X)=0$.
--   3. It is impossible for unweighted sharing under i.i.d. leakage: for every finite abelian $\mathbb G$, every non-trivial channel $\tau$ and every $d$, $Z=S_0+\dots+S_d$ has $I(Z;X)>0$.
--
--   Here $I$ is the Shannon mutual information in bits.
--
--   Differences from the source:
--
--   - reading: supp λ → the non-trivial characters w with λ(w) ≠ 0; reason: λ is defined on the non-trivial characters (Definition 1); with w = 0 included, λ(0) = 1 would put 0 in every (A_i*)^{-1}(supp λ) and the iff would contradict Proposition 2
--   - encoding: ⋂_i (A_i*)^{-1}(supp λ) = ∅ with A_i* the Fourier-domain representation of φ_i → ¬ ∃ w : NontrivialChar G, ∀ i, fourierEnergy (localJoint τ) (w ∘ φ_i) ≠ 0; reason: A_i* w = w ∘ φ_i as in Eq. (9) (κ_d(φ) = Σ_{w≠0} ∏ q_i(A_i* w)); w ∘ φ_i is non-trivial iff w is
--   - encoding: "non-trivial local leakage channel" → a Markov kernel τ with 0 < shannonMI (localJoint τ); reason: the standing assumption I(S;L) > 0 of §2.1
--   - generalization: "there exist finite abelian groups and non-trivial leakage channels for which this condition is achievable with finitely many shares" → G = ZMod 5, a full-support binary τ with I(S;L) > 0, d = 1 and some φ : Fin 2 → (ZMod 5 ≃+ ZMod 5) with I(Z;X) = 0; reason: the proof's witness (Proposition 2); a named witness implies the printed existential, and I(Z;X) = 0 is equivalent to the condition by clause 1
--   - reading: "whereas it is impossible for non-weighted sharing under i.i.d leakage assumption" → for every finite abelian G, non-trivial Markov τ and d : ℕ, 0 < shannonMI (globalJoint (fun _ => τ) d); reason: §5.3, p. 19 states it so ("I(Z;X) > 0 always holds for all finite d for non-automorphism-weighted sharing with the i.i.d leakage"); by clause 1 with all φ_i = id it is the impossibility of the condition
--   - encoding: the law of (Z, X) for automorphism-weighted sharing (§5.3) → weightedGlobalJoint (fun _ => τ) φ; reason: with all φ_i the identity it is the base globalJoint (verification module)
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Theorem 11, Eq. (12), p. 21; proof p. 22; Eq. (9), p. 20; §5.3, p. 19

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
import Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

/-- Ueno, STOC 2027 submission #326, Theorem 11, p. 21 (proof p. 22): spectral de-alignment and
finite-share perfect leakage cancellation.
(i) For a finite abelian group `G`, a non-trivial channel `τ` (`I(S; L) > 0`) with Fourier power
spectrum `λ`, and automorphisms `φ₀, …, φ_d`: `I(Z; X) = 0` for `Z = ∑ φ_i(S_i)` iff
`⋂_i (A_i^*)^{-1}(supp λ) = ∅`, where `A_i^* w = w ∘ φ_i` and `supp λ = {w ≠ 0 : λ(w) ≠ 0}`.
(ii) This is achievable with finitely many shares: on `ℤ₅` with two shares there are a full-support
non-trivial binary channel and automorphisms with `I(Z; X) = 0`.
(iii) It is impossible for non-weighted sharing under i.i.d. leakage: for every finite abelian `G`,
non-trivial `τ` and `d`, `I(Z; X) > 0` for `Z = S₀ + ⋯ + S_d`. -/
theorem theorem_11 :
    (∀ {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
        {L : Type*} [MeasurableSpace L] (τ : Kernel G L) [IsMarkovKernel τ],
        0 < shannonMI (localJoint τ) → ∀ (d : ℕ) (φ : Fin (d + 1) → (G ≃+ G)),
          (shannonMI (weightedGlobalJoint (fun _ : ℕ => τ) φ) = 0 ↔
            ¬ ∃ w : NontrivialChar G, ∀ i,
              fourierEnergy (localJoint τ) (w.1.compAddMonoidHom (φ i).toAddMonoidHom) ≠ 0)) ∧
    (∃ τ : Kernel (ZMod 5) Bool, IsMarkovKernel τ ∧ FullSupport τ ∧ 0 < shannonMI (localJoint τ) ∧
      ∃ φ : Fin 2 → (ZMod 5 ≃+ ZMod 5), shannonMI (weightedGlobalJoint (fun _ : ℕ => τ) φ) = 0) ∧
    (∀ {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
        {L : Type*} [MeasurableSpace L] (τ : Kernel G L) [IsMarkovKernel τ],
        0 < shannonMI (localJoint τ) → ∀ d : ℕ, 0 < shannonMI (globalJoint (fun _ : ℕ => τ) d)) := by sorry

end LeakageSpectral.Shannon.Supplement
