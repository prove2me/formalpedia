-- Prove2me | Theorems.Thm_GaussOptCVQKD_first_moments_no_role
-- name    : GaussOptCVQKD.first_moments_no_role
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:01:43.438991+00:00
-- url     : https://prove2.me/theorems/e6a487fa-d272-4fd4-9762-c0935655759a
-- title:
--   p.1 — the first-order moments play no role: $K_\beta$ and its pieces are invariant under local displacements
-- statement:
--   Let $\rho$ be a density of a finite set of bosonic modes owned by Alice and Bob, and let $W(\zeta)=e^{i\zeta\cdot R}$ be a displacement (a product of single-mode Weyl operators, hence a local operation). Then the displaced state $W(\zeta)\rho W(\zeta)^\dagger$, which has the same covariance matrix and first moments shifted by $\zeta$-dependent amounts, has
--
--   1. the same outcome mutual information $S(a{:}b)$,
--   2. the same entropy $S(\rho_{AB})$,
--   3. the same averaged conditional entropies $\int p(a)S(\rho^a_B)\,da$ and $\int p(b)S(\rho^b_A)\,db$,
--   4. the same key rate $K_\beta$,
--
--   for every $\beta\in[0,1]$, both reconciliation directions and every choice of homodyne/heterodyne measurements:
--   $$
--   K_\beta\bigl(W(\zeta)\rho W(\zeta)^\dagger\bigr)=K_\beta(\rho).
--   $$
--
--   This is why the covariance matrix alone determines the optimal attack (p.1): a Gaussian state with the covariance of $\rho$ can be compared with $\rho$ whatever its first moments.
--
--   **Formalization Note** The pieces are compared in $[0,\infty]$, with no finiteness assumption.
--
--   Differences from the source:
--
--   - reading: 'γAB completely characterizes the channel as the first-order moments of the quadratures do not play any role' → K_β and each of its three pieces are unchanged by every displacement W(ζ)ρW(ζ)† of the state; reason: displacements change exactly the first moments and keep γ; this is the mathematical content of the sentence, used to pass from centered states to arbitrary ones
--   - generalization: one mode per party ((6)), or N modes per party ((7)) → every finite mode set I with every owner map I → {Alice, Bob}; reason: N = 1 or N modes on each side is the special case of an owner map with one or N modes per party
--   - generalization: direct reconciliation with perfect efficiency, K = S(a:b) − S(a:E) ((6)) → both directions (DR, and RR with a ↔ b, A ↔ B, p.3) and every reconciliation efficiency β ∈ [0, 1] (K = βS(a:b) − S(a:E), (11), p.4); reason: the paper extends its claim to RR (p.3) and to (11) (p.4) in prose; β = 1 with DR is (6)
--   - encoding: entropies and mutual information as real numbers → in nats, valued in [0, ∞] (Mathlib klDiv, published extendedEntropyNats), converted to reals in K; reason: same values where finite; the statement concludes or assumes the finiteness it needs
--   - encoding: quadratures x, p and the heterodyne outcome α → x = (a + a†)/√2, vacuum covariance I (Support50.P14); heterodyne outcome recorded as √2(Re α, Im α); outcome laws and conditional states characterized by characteristic functions; reason: Lean convention; mutual information and Holevo quantities are invariant under an invertible linear relabelling of outcomes
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, p.1, 'the first-order moments of the quadratures do not play any role'

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_GaussOptCVQKD_MeasurementModel
import Definitions.Def_GaussOptCVQKD_KeyRate

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)
open QAlgorithms.Papers.Independent.Support50.P14 (InterleavedQuadrature oscillatorWeylKernel)

namespace GaussOptCVQKD

/-- **The first-order moments play no role**, García-Patrón, Cerf, arXiv:quant-ph/0608032v1,
p.1: "The optimal attack being Gaussian (as we will prove below), γAB completely characterizes
the channel as the first-order moments of the quadratures do not play any role."

For every density `ρ` and every displacement `W(ζ)` (a product of single-mode Weyl operators,
hence local to Alice and Bob), the displaced state `W(ζ) ρ W(ζ)†` has the same outcome mutual
information, the same entropy, the same averaged conditional entropies (both directions) and the
same key rate `K_β`, for every `β ∈ [0,1]`, reconciliation direction and measurement choice.

**Formalization Note** The pieces are compared in `ℝ≥0∞`, with no finiteness assumption. -/
theorem first_moments_no_role (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (r : Reconciliation)
    (mA mB : Measurement) {I : Type} [Fintype I] (owner : I → Fin 2) (ρ : State (Occupation I))
    (ζ : InterleavedQuadrature I → ℝ) :
    mutualInfo owner ![mA, mB] (conjugateKernel (oscillatorWeylKernel ζ) ρ.coefficients) =
        mutualInfo owner ![mA, mB] ρ.coefficients ∧
      extendedEntropyNats (conjugateKernel (oscillatorWeylKernel ζ) ρ.coefficients) =
        extendedEntropyNats ρ.coefficients ∧
      (∀ p q : Fin 2, p ≠ q →
        holevoIntegral owner ![mA, mB] (conjugateKernel (oscillatorWeylKernel ζ) ρ.coefficients)
            p q =
          holevoIntegral owner ![mA, mB] ρ.coefficients p q) ∧
      keyRate β r mA mB I owner (conjugateKernel (oscillatorWeylKernel ζ) ρ.coefficients) =
        keyRate β r mA mB I owner ρ.coefficients := by sorry

end GaussOptCVQKD
