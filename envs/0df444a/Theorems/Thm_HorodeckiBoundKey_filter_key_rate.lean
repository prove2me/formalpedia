-- Prove2me | Theorems.Thm_HorodeckiBoundKey_filter_key_rate
-- name    : HorodeckiBoundKey.filter_key_rate
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:04.019889+00:00
-- url     : https://prove2.me/theorems/efec8f73-0f31-45f7-926e-50cba7c73753
-- title:
--   Key from a local filter on $n$-blocks counts for the input: $K(\rho)\ge \tfrac qn K(\sigma)$
-- statement:
--   Let $\rho$ be a state on $A B A' B'$ (one key qubit per party, finite shields) and $n\ge 1$. Let $F_A$ map Alice's $n$ key qubits and shields to one key qubit and a shield $S'$, and $F_B$ likewise for Bob, with
--   $$
--   F_A^\dagger F_A\le\mathbb 1,\qquad F_B^\dagger F_B\le\mathbb 1 .
--   $$
--   If $(F_A\otimes F_B)\,\rho^{\otimes n}\,(F_A\otimes F_B)^\dagger = q\,\sigma$ for some $q>0$ and some state $\sigma$, then
--   $$
--   K(\rho)\;\ge\;\frac{q}{n}\,K(\sigma),
--   $$
--   where $K$ is the distillable key across $AA':BB'$.
--
--   The paper uses this step without stating it: after the recurrence step on $n$ copies of (11) succeeds with probability $N$, the key drawn from $\rho'$ is key drawn from $\rho$ (p.3, "we now show that Alice and Bob can draw key at a nonzero asymptotic rate"). Applied with $F_A\otimes F_B = J_A^\dagger\otimes J_B^\dagger\otimes\mathbb 1$ and $q = N$, it transfers a positive key rate of $\rho'$ to $\rho$.
--
--   **Formalization Note** $K$ is the operational private-dit rate `Gap48.P42.distillableKey` of `finCut`, valued in $[0,\infty]$; $\rho^{\otimes n}$ is `keyPower` and $F_A\otimes F_B$ is `localPair`. Shield types live in `Type`.
--
--   Differences from the source:
--   - reading: the implicit step that key distilled from ρ′ counts as key from ρ → K(ρ) ≥ (q/n)·K(σ) for a local filter succeeding with weight q on n-blocks; reason: the quantitative form of the step: the filter is applied to blocks of n copies and succeeds with frequency q
--   - generalization: the recurrence branch J† ⊗ J† ⊗ 1 on n copies of the state (11) → any local filter F_A ⊗ F_B with F†F ≤ 1 on n copies of any finite key-and-shield state; reason: specializes to the recurrence branch of (12) with q = N
--   - reading: distillable key K_D (key drawn by local operations and public communication; not defined formally in the paper) → K_γ, the operational private-dit rate Gap48.P42.distillableKey under deterministic finite adaptive LOCC (ℝ≥0∞); reason: p.2 identifies the two rates ("We thus have equality of the two rates", with "Clearly K_γ ≤ K_D") and the proof on p.3 distils γ states "at the same rate as K_D"; the mission uses this one key rate throughout
--   - encoding: the Alice:Bob cut AA′:BB′ of a state on A B A′ B′ → finCut: partyCut followed by a fixed relabelling of Alice's register Fin 2 × A′ as Fin (2|A′|) and Bob's likewise; reason: the published rates take matrices on Fin a × Fin b; rates, separability and partial transposition are invariant under local relabellings
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.3 ("Now, we take n copies, and apply the recurrence distillation protocol of [23] without the twirling step"; "Alice and Bob can draw key at a nonzero asymptotic rate")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_HorodeckiBoundKey_finCut
import Definitions.Def_HorodeckiBoundKey_keyPower
import Definitions.Def_HorodeckiBoundKey_localPair

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)
open QAlgorithms.Papers.Independent.Gap48.P42 (distillableKey)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.3 ("Now, we take n
copies, and apply the recurrence distillation protocol of [23] without the twirling step";
"Alice and Bob can draw key at a nonzero asymptotic rate"): key distilled from the output of a
local filter on blocks of `n` copies counts for the input state, at the filter's success rate.

Let `ρ` be a state on `A B A′ B′` and `n ≥ 1`. Let `F_A` (Alice's `n` key qubits and shields →
one key qubit and shield `S′`) and `F_B` (Bob's, likewise) be local operators with
`F_A†F_A ≤ 𝟙` and `F_B†F_B ≤ 𝟙`. If `(F_A ⊗ F_B) ρ^{⊗n} (F_A ⊗ F_B)† = q σ` with `q > 0` and `σ` a
state, then
`K(ρ) ≥ (q/n) · K(σ)`.

The paper uses this step without stating it: the key drawn from `ρ′` of (12) is key drawn from
`ρ` of (11).

**Formalization Note.** Rates are `Gap48.P42.distillableKey` (`K_γ`, `ℝ≥0∞`) across the
Alice:Bob cut `AA′ : BB′` (`finCut`). `F_A ⊗ F_B` is `localPair F_A F_B`, applied to `keyPower ρ n`.
The shield types are in `Type` (universe 0). -/
theorem filter_key_rate {S T S' T' : Type} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] [Fintype S'] [DecidableEq S'] [Fintype T'] [DecidableEq T']
    (ρ : Op (Key 2 × (S × T))) (hρ : IsDensityMatrix ρ) (n : ℕ) (hn : 1 ≤ n)
    (FA : Matrix (Fin 2 × S') ((Fin n → Fin 2) × (Fin n → S)) ℂ)
    (FB : Matrix (Fin 2 × T') ((Fin n → Fin 2) × (Fin n → T)) ℂ)
    (hFA : (1 - FAᴴ * FA).PosSemidef) (hFB : (1 - FBᴴ * FB).PosSemidef)
    (q : ℝ) (hq : 0 < q) (σ : Op (Key 2 × (S' × T'))) (hσ : IsDensityMatrix σ)
    (hfilter : localPair FA FB * keyPower ρ n * (localPair FA FB)ᴴ = (q : ℂ) • σ) :
    ENNReal.ofReal (q / n) * distillableKey (finCut σ) ≤ distillableKey (finCut ρ) := by sorry

end HorodeckiBoundKey
