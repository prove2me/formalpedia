-- Prove2me | Theorems.Thm_GaussOptCVQKD_property_iii_strong_superadditivity
-- name    : GaussOptCVQKD.property_iii_strong_superadditivity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:01:16.524138+00:00
-- url     : https://prove2.me/theorems/bb0c4a86-45de-4701-90c4-c3dde6dfca92
-- title:
--   Property iii) and (10) — strong super-additivity of $K_\beta$, with additivity on product states
-- statement:
--   Fix $\beta\in[0,1]$, a reconciliation direction and the measurement choices of Alice and Bob. Let $X$ and $Y$ be finite sets of modes, each mode owned by Alice or Bob (a block may contain modes of both). Then:
--
--   1. for every density $\rho$ of the modes $X\sqcup Y$ with finite mean photon number, with marginals $\rho_X$, $\rho_Y$,
--   $$
--   K_\beta(\rho_X)+K_\beta(\rho_Y)\le K_\beta(\rho);
--   $$
--   2. for densities $\sigma$ of $X$ and $\tau$ of $Y$ with finite mean photon number,
--   $$
--   K_\beta(\sigma\otimes\tau)=K_\beta(\sigma)+K_\beta(\tau).
--   $$
--
--   With $X=A_1B_1$ and $Y=A_2B_2$ this is (10), $K(\rho_{A_{1,2}B_{1,2}})\ge K(\rho_{A_1B_1})+K(\rho_{A_2B_2})$, together with the additivity on products stated after it.
--
--   **Formalization Note** Finite mean photon number makes the three pieces of $K_\beta$ finite for the state and its marginals, so the real-valued $K$ is the paper's $K$ on both sides.
--
--   Differences from the source:
--
--   - generalization: two modes on each side, A1,2 and B1,2 ('the generalization to N > 2 being straightforward') → any split of any finite mode set into two blocks X, Y, each with any owner map; reason: X = A1B1, Y = A2B2 is (10); iterating gives the N-block form
--   - reading: states for which the conditional entropies of (8)–(9) are defined → densities of finite mean photon number; reason: (8)–(9) subtract conditional entropies, which must be finite; every state with a covariance matrix (the paper's standing setting) has finite mean photon number, and marginals and passive unitaries preserve it
--   - generalization: direct reconciliation with perfect efficiency, K = S(a:b) − S(a:E) ((6)) → both directions (DR, and RR with a ↔ b, A ↔ B, p.3) and every reconciliation efficiency β ∈ [0, 1] (K = βS(a:b) − S(a:E), (11), p.4); reason: the paper extends its claim to RR (p.3) and to (11) (p.4) in prose; β = 1 with DR is (6)
--   - encoding: entropies and mutual information as real numbers → in nats, valued in [0, ∞] (Mathlib klDiv, published extendedEntropyNats), converted to reals in K; reason: same values where finite; the statement concludes or assumes the finiteness it needs
--   - encoding: quadratures x, p and the heterodyne outcome α → x = (a + a†)/√2, vacuum covariance I (Support50.P14); heterodyne outcome recorded as √2(Re α, Im α); outcome laws and conditional states characterized by characteristic functions; reason: Lean convention; mutual information and Holevo quantities are invariant under an invertible linear relabelling of outcomes
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, 'Optimality of Gaussian attacks', property iii) Strong super-additivity, (10) and the additivity sentence, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_GaussOptCVQKD_MeasurementModel
import Definitions.Def_GaussOptCVQKD_KeyRate

open scoped ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Support50.P14 (photonEnergy marginalFirst marginalSecond oscillatorTensor)

namespace GaussOptCVQKD

/-- **Property iii) Strong super-additivity, (10), and additivity on products**, García-Patrón,
Cerf, arXiv:quant-ph/0608032v1, "Optimality of Gaussian attacks", p.3: "iii) Strong
super-additivity: We will restrict the proof to two modes on each side, A1,2 and B1,2, the
generalization to N > 2 being straightforward", (10) `K(ρ_{A1,2B1,2}) ≥ K(ρ_{A1B1}) + K(ρ_{A2B2})`,
and "The additivity of K(ρA1,2B1,2) is a straightforward consequence of the additivity of von
Neumann entropies."

For every `β ∈ [0, 1]`, direction `r` and measurement choices `mA`, `mB`, and all finite mode sets
`X`, `Y` with owner maps `ox`, `oy`:
1. for every density `ρ` of finite mean photon number on the modes `X ⊕ Y`,
   `K_β(ρ_X) + K_β(ρ_Y) ≤ K_β(ρ_{X⊕Y})`, with `ρ_X`, `ρ_Y` the two marginals;
2. for densities `σ` on `X` and `τ` on `Y` of finite mean photon number,
   `K_β(σ ⊗ τ) = K_β(σ) + K_β(τ)`.

**Formalization Note** Each block may hold modes of both parties (the owner map on `X ⊕ Y` is
`Sum.elim ox oy`). Finite mean photon number makes every piece of `K_β` finite, so the real-valued
`K` is the paper's `K` on both sides. -/
theorem property_iii_strong_superadditivity (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (r : Reconciliation) (mA mB : Measurement) :
    (∀ (X Y : Type) [Fintype X] [Fintype Y] (ox : X → Fin 2) (oy : Y → Fin 2)
      (ρ : State (Occupation (X ⊕ Y))), photonEnergy ρ.coefficients < ⊤ →
      keyRate β r mA mB X ox (marginalFirst ρ.coefficients) +
          keyRate β r mA mB Y oy (marginalSecond ρ.coefficients) ≤
        keyRate β r mA mB (X ⊕ Y) (Sum.elim ox oy) ρ.coefficients) ∧
    ∀ (X Y : Type) [Fintype X] [Fintype Y] (ox : X → Fin 2) (oy : Y → Fin 2)
      (σ : State (Occupation X)) (τ : State (Occupation Y)),
      photonEnergy σ.coefficients < ⊤ → photonEnergy τ.coefficients < ⊤ →
      keyRate β r mA mB (X ⊕ Y) (Sum.elim ox oy) (oscillatorTensor σ.coefficients τ.coefficients) =
        keyRate β r mA mB X ox σ.coefficients + keyRate β r mA mB Y oy τ.coefficients := by sorry

end GaussOptCVQKD
