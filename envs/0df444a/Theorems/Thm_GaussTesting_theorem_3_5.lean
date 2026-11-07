-- Prove2me | Theorems.Thm_GaussTesting_theorem_3_5
-- name    : GaussTesting.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:48.693635+00:00
-- url     : https://prove2.me/theorems/b8f7e39d-f3d5-46e1-8d77-761611c0f380
-- title:
--   Theorem 3.5 — soundness from spectral gaps: $\alpha\,\mathrm{dist}(\psi,\mathcal C)^2\le q(\psi)\le k\,\mathrm{dist}(\psi,\mathcal C)^2$
-- statement:
--   Let $\mathcal C$ be a nonempty class of pure states on a Hilbert space $\mathcal H$, and let $\Pi_{\mathrm{test}}$ be a permutation-invariant orthogonal projector on $\mathcal H^{\otimes k}$, $k\ge2$, such that
--
--   $$
--   \Pi_{\mathrm{test}}|\psi\rangle^{\otimes k}=|\psi\rangle^{\otimes k}\iff|\psi\rangle\in\mathcal C .
--   $$
--
--   Suppose that the symmetrized operator $\Xi=\Pi^{(1,\dots,m)}_{\mathrm{sym}}\Pi^{(1,\dots,k)}_{\mathrm{test}}\Pi^{(1,\dots,m)}_{\mathrm{sym}}$ on $m>k$ registers has spectral gap at least $\Delta$, where
--
--   $$
--   \frac{k(k-1)}{m(m-1)}<\Delta\le1 .\qquad(3.40)
--   $$
--
--   Then for every pure state $\psi$, with $\varepsilon=\mathrm{dist}(\psi,\mathcal C)$ and $q(\psi)=1-\mathrm{tr}(\Pi_{\mathrm{test}}\psi^{\otimes k})$,
--
--   $$
--   \alpha\varepsilon^2\le q(\psi)\le k\varepsilon^2,\qquad \alpha=\min\Big\{\frac12,\ \frac{m(m-1)\Delta-k(k-1)}{(m-k)(m+k-1)}\Big\}.\qquad(3.41)
--   $$
--
--   This is the paper's general framework: a spectral gap of the symmetrized test operator yields quadratic soundness of the test, uniformly over the Hilbert space.
--
--   Differences from the source:
--   - encoding: a Hilbert space ℋ → ℓ²(ι) for an arbitrary index type ι, with ℋ^{⊗k} = ℓ²(Fin k → ι); reason: every Hilbert space is isometric to ℓ² of an orthonormal basis
--   - encoding: a permutation-invariant orthogonal projector Π_test on ℋ^{⊗k} → a closed subspace K ⊆ ℋ^{⊗k} invariant under every register permutation, Π_test = proj K; reason: a projector commutes with the permutations iff its range is invariant under them
--   - reading: spectral gap at least Δ (Definition 3.1: smallest nonzero eigenvalue of I − Ξ) → every nonzero point z of spectrum ℂ (I − Ξ) has Δ ≤ Re z; reason: in finite dimension the same; in infinite dimension the spectral form is what the proof uses (T² ⪰ ΔT)
--   - encoding: m > k registers → Ξ = xi K (m − k) on ℓ²(Fin (k + (m − k)) → ι); reason: the added registers are counted by m − k ≥ 1
--   - encoding: a class 𝒞 of pure states; pure states |ψ⟩ ∈ ℋ → a set C of unit vectors (∀ φ ∈ C, ‖φ‖ = 1); unit vectors ψ; reason: a pure state is a unit vector of ℋ
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Theorem 3.5, eqs. (3.40)–(3.41), p.26; Definition 3.1, p.21

import Definitions.Def_GaussTesting_xi
import Definitions.Def_GaussTesting_HasGapAtLeast
import Definitions.Def_GaussTesting_distTo
import Definitions.Def_GaussTesting_rejProb

namespace GaussTesting

/-- **Theorem 3.5 (Soundness from spectral gaps).** Let `𝒞` be a nonempty class of pure states on
`ℋ = ℓ²(ι)` and `Π_test = Π_K` a permutation-invariant orthogonal projector on `ℋ^{⊗k}`, `k ≥ 2`, such that
`Π_test |ψ⟩^{⊗k} = |ψ⟩^{⊗k}` iff `|ψ⟩ ∈ 𝒞`. If the symmetrized operator `Ξ` on `m > k` registers has
spectral gap at least `Δ`, where `k(k−1)/(m(m−1)) < Δ ≤ 1` (3.40), then for every pure state `ψ`, with
`ε = dist(ψ, 𝒞)`, `αε² ≤ q(ψ) ≤ kε²`, where
`α = min{1/2, (m(m−1)Δ − k(k−1))/((m−k)(m+k−1))}` (3.41).

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Theorem 3.5, eqs. (3.40)–(3.41), p.26; Definition 3.1, p.21.

**Formalization Note.** The Hilbert space is `ℓ²(ι)` for an arbitrary index type (every Hilbert space is
of this form). `Ξ = xi K (m − k)` acts on `ℓ²(Fin (k + (m − k)) → ι) = ℋ^{⊗m}`. Permutation invariance
of `Π_K` is invariance of `K` under all register permutations. "Spectral gap at least `Δ`" is
`HasGapAtLeast` (spectrum of `I − Ξ`). -/
theorem theorem_3_5 {ι : Type*} (C : Set (Ell2 ι)) (k m : ℕ)
    (K : ClosedSubmodule ℂ (Ell2 (Fin k → ι))) (Δ : ℝ)
    (hC : C.Nonempty) (hCunit : ∀ φ ∈ C, ‖φ‖ = 1) (hk : 2 ≤ k) (hkm : k < m)
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∀ f ∈ K, permVec σ f ∈ K)
    (hiff : ∀ ψ : Ell2 ι, ‖ψ‖ = 1 → (proj K (tpow k ψ) = tpow k ψ ↔ ψ ∈ C))
    (hΔlo : (k : ℝ) * (k - 1) / ((m : ℝ) * (m - 1)) < Δ) (hΔhi : Δ ≤ 1)
    (hgap : HasGapAtLeast (xi K (m - k)) Δ) :
    ∀ ψ : Ell2 ι, ‖ψ‖ = 1 →
      min (1 / 2) (((m : ℝ) * (m - 1) * Δ - k * (k - 1)) / (((m : ℝ) - k) * (m + k - 1))) *
          distTo ψ C ^ 2 ≤ rejProb K ψ ∧
        rejProb K ψ ≤ k * distTo ψ C ^ 2 := by sorry

end GaussTesting
