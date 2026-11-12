-- Prove2me | Theorems.Thm_ImpuritySim_lemma_3_2
-- name    : ImpuritySim.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:06.741876+00:00
-- url     : https://prove2.me/theorems/72877e2c-9c7d-4f8f-a335-23ef49c2ab36
-- title:
--   Lemma 3.2 — weighted positivity $\mathrm{Re}(e^{-\lambda D_\ell}E_\ell e^{\lambda D_\ell})\ge\frac{\omega_\ell}2I$ for $0<\lambda\le1/4$
-- statement:
--   Let $\{h_d\}_{d\ge1}$ be real numbers with $h_1=0$ and $|h_{d+1}-h_d|\le1$. For a Hamiltonian in the form (3.15), every band $\ell\in\{0,\dots,L\}$, the depth-weighted operator $D_\ell=\sum_{d\ge1}h_d\Pi_{\ell,d}$ (3.19) and every $0<\lambda\le1/4$,
--   $$\operatorname{Re}\bigl(e^{-\lambda D_\ell}E_\ell e^{\lambda D_\ell}\bigr)\ \ge\ \frac{\omega_\ell}2\,I,\qquad(3.20)$$
--   where $\operatorname{Re}(X)=(X+X^\dagger)/2$ and $\ge$ is the Loewner order.
--
--   The similarity transform by $e^{\lambda D_\ell}$ distorts $E_\ell$ only on the off-diagonal depth blocks, so it keeps half of the lower bound $E_\ell\ge\omega_\ell I$; this is the input to the bath-energy bound (Lemma 4.5).
--
--   **Formalization Note** $E_\ell$ is the block of $E$ on the band-$\ell$ residual-bath modes and $D_\ell$ the diagonal matrix of their weights $h_{d(i)}$, so $e^{\pm\lambda D_\ell}$ is diagonal. No sign condition on $h$ is assumed (the lemma has none).
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
--   - encoding: e^{±λD_ℓ}, D_ℓ = Σ_{d≥1} h_d Π_{ℓ,d} → the diagonal matrices of e^{±λ h_{d(i)}} on the band-ℓ bath modes; reason: Π_{ℓ,d} are the coordinate projectors of the Krylov basis, so D_ℓ is diagonal
--   - encoding: A ≥ (ω_ℓ/2) I → (A − (ω_ℓ/2)·1).PosSemidef; reason: the Loewner order
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Lemma 3.2, Eqs. (3.19)–(3.20), pp.18–19

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix
open scoped ComplexOrder

namespace ImpuritySim

/-- **Lemma 3.2 (Weighted positivity of the bath)**, pp.18–19, of J. Jiang, N. Ju, O. Parekh,
C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum impurity models*,
arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eqs. (3.19)–(3.20).

Let `{h_d}_{d ≥ 1}` be real numbers with `h_1 = 0` and `|h_{d+1} − h_d| ≤ 1`. For every band `ℓ` of
an impurity Hamiltonian in the form (3.15), with `D_ℓ = Σ_{d ≥ 1} h_d Π_{ℓ,d}` (3.19), and every
`0 < λ ≤ 1/4`,
`Re(e^{−λD_ℓ} E_ℓ e^{λD_ℓ}) ≥ (ω_ℓ/2) I` (3.20).

**Formalization Note.** `E_ℓ` is the band-`ℓ` block of `E` on the band-`ℓ` residual-bath modes,
`D_ℓ` the diagonal matrix of their weights `h_{d(i)}`, so `e^{±λD_ℓ}` is diagonal (`simE`);
`Re(X) = (X + X†)/2` (`reSimE`), and `≥` is the Loewner order (`PosSemidef` of the difference).
The bands are `ℓ = 0, …, L`. No sign condition on `h` is assumed (the page assumes none). -/
theorem lemma_3_2 {n : ℕ} (F : BandwiseForm n) (h : ℕ → ℝ) (h1 : h 1 = 0)
    (hstep : ∀ d, 1 ≤ d → |h (d + 1) - h d| ≤ 1) (ℓ : ℕ) (hℓ : ℓ ≤ F.L)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 4) :
    (F.reSimE h lam ℓ -
      ((F.omegaL ℓ / 2 : ℝ) : ℂ) • (1 : Matrix (F.bandIdx ℓ) (F.bandIdx ℓ) ℂ)).PosSemidef := by sorry

end ImpuritySim
