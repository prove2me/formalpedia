-- Prove2me | Theorems.Thm_ImpuritySim_Supplement_theorem_6_3
-- name    : ImpuritySim.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:32:53.310889+00:00
-- url     : https://prove2.me/theorems/336c0a37-d2ef-4d58-ac22-272f667803ec
-- title:
--   Theorem 6.3 — $\mathrm{Tr}(\rho^{(\beta)}e^{D^{(\beta)}/2})\le e^{8\kappa}(1+4\eta_\tau e^{\eta_\tau}/(e\beta\omega))$ and $\eta_\tau\le n\,e^{-\beta\omega/8+\tau/2}$
-- statement:
--   Let $H$ be an impurity Hamiltonian in the form (3.15) on $n$ modes, let $\beta>0$, and let
--   $$\rho^{(\beta)}=\frac{e^{-\beta H}}{\operatorname{Tr}e^{-\beta H}}$$
--   be its thermal state. Fix a cutoff $\tau\ge1$, let $D^{(\beta)}=\sum_i\min\{d(i)-1,\tau\}\,n_i$ (6.1), let $\kappa=\sum_{\ell=0}^L\xi_\ell/\omega_\ell^2$ as defined in (3.17), and let $\eta_\tau=\sum_i\exp\bigl(-\beta\omega_{\ell(i)}/8+\tfrac12\min\{d(i)-1,\tau\}\bigr)$, the sums over the residual-bath modes. Then
--
--   1. $$\operatorname{Tr}\Bigl(\rho^{(\beta)}e^{\frac12D^{(\beta)}}\Bigr)\le e^{8\kappa}\Bigl(1+\frac{4\eta_\tau e^{\eta_\tau}}{e\beta\omega}\Bigr),\qquad(6.13)$$
--   where $e$ is Euler's number;
--   2. $$\eta_\tau\le n\exp\Bigl(-\frac{\beta\omega}{8}+\frac\tau2\Bigr).\qquad(6.14)$$
--
--   This is the thermal counterpart of Theorem 5.1: in the thermally gapped regime it bounds the exponential moment of the capped depth, which the compression of the thermal state turns into a polynomial-size support.
--
--   **Formalization Note** The thermal state is the published `WolfAreaLaw.thermalState`; the trace, which is real, is compared through its real part.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm (the published data with the properties of (3.15)–(3.18) and Lemma 3.1); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's, exactly as for the published Theorem 5.1
--   - encoding: "at inverse temperature β" → a real β > 0; reason: an inverse temperature is positive (the bound divides by eβω), as in Theorem 6.8 "for any β > 0"
--   - encoding: Σ_i in D^(β) and η_τ → the sum over the residual-bath modes F.bath; reason: ℓ(i), d(i) and the D^(β) of (6.1) are defined on those modes only
--   - encoding: Tr(ρ^(β) e^{D^(β)/2}) → the real part of the trace; reason: the trace is real (ρ^(β) and e^{D^(β)/2} are positive)
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Theorem 6.3, Eqs. (6.13)–(6.14), p.29; (6.1), p.28; (3.17), p.18; proof App. B.4

import Mathlib
import Definitions.Def_ImpuritySim_Supplement_Thermal
import Definitions.Def_WolfAreaLaw_thermalState

namespace ImpuritySim.Supplement

/-- **Theorem 6.3 (Thermal exponential-moment bound for capped Krylov depth)**, p.29, of J. Jiang,
N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum
impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eqs. (6.13)–(6.14),
with (6.1), p.28, and (3.17), p.18.

Let `H` be an impurity Hamiltonian in the form (3.15) on `n` modes, `ρ^(β) = e^{−βH}/Tr e^{−βH}`
its thermal state at inverse temperature `β > 0`, and `τ ≥ 1` a cutoff. With
`D^(β) = Σ_i min{d(i) − 1, τ} n_i` (6.1), `κ` as in (3.17) and
`η_τ = Σ_i exp(−β ω_{ℓ(i)}/8 + ½ min{d(i) − 1, τ})` (6.14):
1. `Tr(ρ^(β) e^{D^(β)/2}) ≤ e^{8κ} (1 + 4 η_τ e^{η_τ} / (e β ω))` (6.13), with `e` Euler's number;
2. `η_τ ≤ n exp(−βω/8 + τ/2)` (6.14).

**Formalization Note.** "The form (3.15)" is the published `BandwiseForm` (as in Theorem 5.1);
`κ` is `F.kappa`, defined exactly by (3.17) (the page's remark `κ = O(m log₂ J/ω)` is not part of
the claim). The thermal state is the published `WolfAreaLaw.thermalState`
(`e^{−βH}/Tr e^{−βH}`, matrix exponential). `e^{D^(β)/2}` is `F.expHalfD (hCap τ)`; the sums over
`i` range over the residual-bath modes. The trace is real; its real part is compared. -/
theorem theorem_6_3 {n : ℕ} (F : BandwiseForm n) (β τ : ℝ) (hβ : 0 < β) (hτ : 1 ≤ τ) :
    (WolfAreaLaw.thermalState β F.H * F.expHalfD (hCap τ)).trace.re ≤
        Real.exp (8 * F.kappa) *
          (1 + 4 * etaTau F β τ * Real.exp (etaTau F β τ) / (Real.exp 1 * β * F.ω)) ∧
      etaTau F β τ ≤ (n : ℝ) * Real.exp (-(β * F.ω) / 8 + τ / 2) := by sorry

end ImpuritySim.Supplement
