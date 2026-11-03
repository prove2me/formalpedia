-- Prove2me | Theorems.Thm_HolevoEntropyGain_gibbs_increase
-- name    : HolevoEntropyGain.gibbs_increase
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:19.819507+00:00
-- url     : https://prove2.me/theorems/c09221bf-dede-4816-9b6b-841e7d571771
-- title:
--   $\exp(-\beta F)\uparrow I$ and $\Phi[\exp(-\beta F)]\uparrow\Phi[I]$ as $\beta\to0$
-- statement:
--   Let $F\ge0$ be a selfadjoint operator, with eigenbasis $(e_n)$ and eigenvalues $E_n\ge0$, satisfying (5): $\operatorname{Tr}\exp(-\beta F)<\infty$ for $\beta>0$. When $\beta\to0$,
--
--   1. $\exp(-\beta F)\uparrow I$: the quadratic forms $\langle\psi,\exp(-\beta F)\psi\rangle$ increase as $\beta$ decreases, and $\exp(-\beta F)\psi\to\psi$ for every $\psi$;
--   2. for every channel $\Phi$ the quadratic forms of $\Phi[\exp(-\beta F)]$ increase as $\beta$ decreases, and for every countable Kraus representation $(V_j)$ of $\Phi$ and every $\psi$,
--   $$
--   \langle\psi,\Phi[\exp(-\beta F)]\psi\rangle \to \sum_j\|V_j^*\psi\|^2\in[0,+\infty];
--   $$
--   3. for a regular channel, $\Phi[\exp(-\beta F)]\uparrow\Phi[I]$: $\Phi[\exp(-\beta F)]\psi\to\Phi[I]\psi$ for every $\psi$.
--
--   Clause 3 is the printed remark; clause 2 extends it to all channels and is what the proof of Proposition 2 uses to see that a Gaussian channel is regular.
--
--   **Formalization Note** $\uparrow$ (p.2) is monotone convergence of positive operators, weakly and hence strongly; monotonicity is stated on quadratic forms. By (5) each $\exp(-\beta F)$ is trace class, so $\Phi[\exp(-\beta F)]$ is trace class and is realized as a bounded operator.
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H; operators on it → ℓ²(I) for a type I with [Countable I], operators as coefficient arrays in the canonical basis; reason: every separable Hilbert space is unitarily ℓ²(I) for a countable I; the same instances
--   - encoding: F ≥ 0 selfadjoint with (5) → spectral data: an orthonormal basis (eₙ) and Eₙ ≥ 0 with Σₙ e^{−βEₙ} summable for β > 0; reason: (5) forces discrete spectrum, so every such F is of this form
--   - encoding: A_β ↑ A as β → 0 → quadratic forms monotone in β > 0 and strong convergence along β ↓ 0; reason: for an increasing bounded family of positive operators weak and strong convergence coincide (p.2)
--   - generalization: for a regular channel, Φ[exp(−βF)] ↑ Φ[I] → additionally, for every channel and every countable Kraus representation, the forms increase to Σⱼ‖Vⱼ*ψ‖² in [0, ∞]; reason: specializes to the printed remark (clause 3, also stated); the general form is used for regularity in Proposition 2's proof
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, unnumbered remark after (6), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_HolevoEntropyGain_gibbsOperator
import Definitions.Def_HolevoEntropyGain_IsRegularWith

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (IsKrausRepresentation boundedOperator)
open Filter Topology

namespace HolevoEntropyGain

/-- For a positive selfadjoint `F` with (5): `exp(-βF) ↑ I` as `β → 0`, and for a regular channel
`Φ[exp(-βF)] ↑ Φ[I]` (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, unnumbered remark, p.3, PDF p.3).

More generally, for every channel and every Kraus representation, the quadratic forms of `Φ[exp(-βF)]`
increase to `∑ⱼ ‖Vⱼ*ψ‖² ∈ [0, ∞]`; the proof of Proposition 2 uses this to obtain regularity.

**Formalization Note** `↑` (p.2) is monotone convergence of positive operators, weakly and hence
strongly. Monotonicity is stated on quadratic forms. `F` is spectral data with `Eₙ ≥ 0`. By (5) each
`exp(-βF)` is trace class, so `Φ[exp(-βF)]` is trace class and `boundedOperator` is its realization. -/
theorem gibbs_increase {I : Type} [Countable I] (e : HilbertBasis I ℂ (Hilbert I)) (E : I → ℝ)
    (hE0 : ∀ n, 0 ≤ E n) (hE : ∀ β : ℝ, 0 < β → Summable fun n => Real.exp (-β * E n)) :
    (∀ β β' : ℝ, 0 < β → β ≤ β' → ∀ ψ : Hilbert I,
      RCLike.re (inner ℂ ψ (boundedOperator (gibbsOperator e E β') ψ)) ≤
        RCLike.re (inner ℂ ψ (boundedOperator (gibbsOperator e E β) ψ))) ∧
    (∀ ψ : Hilbert I,
      Tendsto (fun β => boundedOperator (gibbsOperator e E β) ψ) (𝓝[>] 0) (𝓝 ψ)) ∧
    ∀ Φ : Channel I I,
      (∀ β β' : ℝ, 0 < β → β ≤ β' → ∀ ψ : Hilbert I,
        RCLike.re (inner ℂ ψ (boundedOperator (Φ.val (gibbsOperator e E β')) ψ)) ≤
          RCLike.re (inner ℂ ψ (boundedOperator (Φ.val (gibbsOperator e E β)) ψ))) ∧
      (∀ (J : Type) [Countable J] (V : J → (Hilbert I →L[ℂ] Hilbert I)),
        IsKrausRepresentation Φ.val V → ∀ ψ : Hilbert I,
          Tendsto (fun β => ENNReal.ofReal
              (RCLike.re (inner ℂ ψ (boundedOperator (Φ.val (gibbsOperator e E β)) ψ))))
            (𝓝[>] 0) (𝓝 (∑' j, ENNReal.ofReal (‖ContinuousLinearMap.adjoint (V j) ψ‖ ^ 2)))) ∧
      (∀ A : Hilbert I →L[ℂ] Hilbert I, IsRegularWith Φ A → ∀ ψ : Hilbert I,
        Tendsto (fun β => boundedOperator (Φ.val (gibbsOperator e E β)) ψ) (𝓝[>] 0) (𝓝 (A ψ))) := by sorry

end HolevoEntropyGain
