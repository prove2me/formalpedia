-- Prove2me | Theorems.Thm_GaussOptCVQKD_holevo_from_rhoAB
-- name    : GaussOptCVQKD.holevo_from_rhoAB
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:01:27.350003+00:00
-- url     : https://prove2.me/theorems/f80b36c6-3263-4f98-ad31-7cb3bacfe2ce
-- title:
--   p.2 — Eve's Holevo bound $\chi_{aE}=S(\rho_E)-\int p(a)S(\rho^a_E)$ equals $S(\rho_{AB})-\int p(a)S(\rho^a_B)$ for every purification
-- statement:
--   Let $\rho_{AB}$ be a density of finitely many bosonic modes owned by Alice and Bob, and let $\Psi$ be any purification of $\rho_{AB}$ held by Eve, on $\mathcal H_{AB}\otimes\ell^2(J)$. Let party $p$ measure its modes (homodyne $x$, homodyne $p$ or heterodyne) and obtain $a$, and let $q\neq p$ be the other party (its modes form $B$). Then:
--
--   1. $S(\rho_E)=S(\rho_{AB})$;
--   2. Eve's averaged conditional entropy equals that of the other party:
--   $$
--   \int da\,p(a)\,S(\rho^a_E)=\int da\,p(a)\,S(\rho^a_B),
--   $$
--   so that
--   $$
--   \chi_{aE}=S(\rho_E)-\int da\,p(a)S(\rho^a_E)=S(\rho_{AB})-\int da\,p(a)S(\rho^a_B);
--   $$
--   3. for every outcome law $\nu$ with conditional states $\rho^a_B$ of $\rho_{AB}$, Eve's conditional states $\rho^a_E$ exist for the same law, and every choice of them satisfies $S(\rho^a_E)=S(\rho^a_B)$ for $\nu$-almost every $a$.
--
--   With $p$ = Alice this is the direct-reconciliation formula of p.2; with $p$ = Bob it is the reverse-reconciliation quantity $\chi_{bE}$. It justifies defining the key rate from $\rho_{AB}$ alone.
--
--   **Formalization Note** All entropies are in nats and valued in $[0,\infty]$; no finiteness is assumed.
--
--   Differences from the source:
--
--   - reading: 'this bound can be calculated from ρAB: for example, when Alice and Bob apply the same measurement, it reads χaE = S(ρAB) − ∫da p(a)S(ρ^a_B)' → the identity for every measurement choice of the measuring party, as S(ρ_E) = S(ρ_AB), equality of the averaged conditional entropies, existence of Eve's conditional states and their a.e. entropy identity; reason: the identity only uses that the measuring party's POVM is rank-one (homodyne and heterodyne both are); 'for example' does not restrict it, and the three clauses are what makes χ_aE computable from ρ_AB
--   - generalization: Alice's outcome a (DR) → either party's outcome (p = Alice: χ_aE; p = Bob: the RR quantity χ_bE); reason: the RR extension of p.3 interchanges a ↔ b, A ↔ B; p = Alice is the printed case
--   - generalization: one mode per party ((6)), or N modes per party ((7)) → every finite mode set I with every owner map I → {Alice, Bob}; reason: N = 1 or N modes on each side is the special case of an owner map with one or N modes per party
--   - encoding: Eve's Hilbert space → ℓ²(J) for an arbitrary index type J; reason: every Hilbert space is ℓ² of an orthonormal basis; the same instances
--   - encoding: entropies as real numbers → in nats, valued in [0, ∞], no finiteness assumed; reason: the identities hold in [0, ∞]; same values where finite
--   - encoding: quadratures x, p and the heterodyne outcome α → x = (a + a†)/√2, vacuum covariance I (Support50.P14); heterodyne outcome recorded as √2(Re α, Im α); outcome laws and conditional states characterized by characteristic functions; reason: Lean convention; mutual information and Holevo quantities are invariant under an invertible linear relabelling of outcomes
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, 'Entanglement-based version of CV-QKD', p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_GaussOptCVQKD_MeasurementModel
import Definitions.Def_GaussOptCVQKD_KeyRate
import Definitions.Def_GaussOptCVQKD_Purification

open MeasureTheory
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorKernel)

namespace GaussOptCVQKD

/-- **Eve's Holevo bound is computable from `ρ_AB`**, García-Patrón, Cerf,
arXiv:quant-ph/0608032v1, "Entanglement-based version of CV-QKD", p.2: "her information is then
limited by the Holevo bound χaE = S(ρE) − ∫da p(a)S(ρ^a_E). Because Eve holds the purification of
ρAB, this bound can be calculated from ρAB: for example, when Alice and Bob apply the same
measurement, it reads χaE = S(ρAB) − ∫da p(a)S(ρ^a_B)."

Let `ρ` be a density on the Fock space of the modes `I` and `Ψ` any purification of `ρ` on
`H_AB ⊗ ℓ²(J)`. Let party `p` measure (its outcome is `a`) and let `q ≠ p` be the other party.
Then
1. `S(ρ_E) = S(ρ_AB)`;
2. Eve's averaged conditional entropy `∫ p(a) S(ρ^a_E)` equals `∫ p(a) S(ρ^a_B)` (with `B` the
   modes of party `q`), so `χ_aE = S(ρ_E) − ∫ p(a) S(ρ^a_E) = S(ρ_AB) − ∫ p(a) S(ρ^a_B)`;
3. for every outcome law `ν` and conditional states `ρ^a_B` of `ρ`, Eve's conditional states
   `ρ^a_E` exist for the same law, and every choice of them has `S(ρ^a_E) = S(ρ^a_B)` for
   `ν`-almost every `a`.
The case `p = 0` is DR (Alice's outcome); `p = 1` is the RR analogue `χ_bE`.

**Formalization Note** Eve's space is `ℓ²(J)` for an arbitrary index type `J`; all entropies
in nats, valued in `[0, ∞]`, with no finiteness assumption. -/
theorem holevo_from_rhoAB {I J : Type} [Fintype I] (owner : I → Fin 2) (mA mB : Measurement)
    (p q : Fin 2) (hpq : p ≠ q) (ρ : State (Occupation I)) (Ψ : Hilbert (Occupation I × J))
    (hΨ : IsPurification Ψ ρ.coefficients) :
    extendedEntropyNats (eveState Ψ) = extendedEntropyNats ρ.coefficients ∧
      eveHolevoIntegral owner ![mA, mB] Ψ p = holevoIntegral owner ![mA, mB] ρ.coefficients p q ∧
      ∀ (ν : Measure (PartyOutcome owner ![mA, mB] p))
        (c : PartyOutcome owner ![mA, mB] p → OscillatorKernel {j : I // owner j = q}),
        IsConditionalFamily owner ![mA, mB] ρ.coefficients p q ν c →
        (∃ cE : PartyOutcome owner ![mA, mB] p → Matrix J J ℂ,
          IsEveConditionalFamily owner ![mA, mB] Ψ p ν cE) ∧
        ∀ cE : PartyOutcome owner ![mA, mB] p → Matrix J J ℂ,
          IsEveConditionalFamily owner ![mA, mB] Ψ p ν cE →
          ∀ᵐ a ∂ν, extendedEntropyNats (cE a) = extendedEntropyNats (c a) := by sorry

end GaussOptCVQKD
