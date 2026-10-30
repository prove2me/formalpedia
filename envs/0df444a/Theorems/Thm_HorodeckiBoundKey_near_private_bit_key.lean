-- Prove2me | Theorems.Thm_HorodeckiBoundKey_near_private_bit_key
-- name    : HorodeckiBoundKey.near_private_bit_key
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:43.732709+00:00
-- url     : https://prove2.me/theorems/f60c8594-8b65-4129-9152-042a3eb6393f
-- title:
--   Devetak–Winter step: a corner norm near $1/2$ gives positive key, uniformly in the shields
-- statement:
--   There is $\varepsilon_0>0$ with the following property. For all finite shields $A'$, $B'$ and every state $\sigma$ on $A B A' B'$ (one key qubit per party) whose $\langle 00|\cdot|11\rangle$ block $X$ satisfies
--   $$
--   \|X\|_1 > \tfrac12-\varepsilon_0,
--   $$
--   the distillable key of $\sigma$ across $AA':BB'$ is strictly positive, $K(\sigma)>0$.
--
--   The paper obtains this from the protocol of Devetak and Winter [8] applied to the measured key of the twisted state and does not prove it. The threshold does not depend on the shields, which matters because the shields of $\rho'$ in (12) grow with $l$ and $n$.
--
--   **Formalization Note** $\varepsilon_0$ is quantified before the shield types. $K$ is `Gap48.P42.distillableKey` of `finCut`, in $[0,\infty]$, so $K>0$ means some positive rate is achievable. Shield types live in `Type`.
--
--   Differences from the source:
--   - reading: "drawing key … from a state close to singlet, which can be done … by the protocol of Devetak and Winter [8]" → ∃ε₀ > 0 such that for all shields every state with corner trace norm > 1/2 − ε₀ has K > 0; reason: the sentence's content for the states it is applied to: their closeness to a private bit is measured by the corner norm (p.2, approximate security), and their shields grow, so one threshold for all shields is needed
--   - reading: distillable key K_D (key drawn by local operations and public communication; not defined formally in the paper) → K_γ, the operational private-dit rate Gap48.P42.distillableKey under deterministic finite adaptive LOCC (ℝ≥0∞); reason: p.2 identifies the two rates ("We thus have equality of the two rates", with "Clearly K_γ ≤ K_D") and the proof on p.3 distils γ states "at the same rate as K_D"; the mission uses this one key rate throughout
--   - encoding: the Alice:Bob cut AA′:BB′ of a state on A B A′ B′ → finCut: partyCut followed by a fixed relabelling of Alice's register Fin 2 × A′ as Fin (2|A′|) and Bob's likewise; reason: the published rates take matrices on Fin a × Fin b; rates, separability and partial transposition are invariant under local relabellings
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.3 ("Clearly, the problem is reduced to drawing key from outcomes of measurement, from a state close to singlet, which can be done, for example, by the protocol of Devetak and Winter [8].")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_HorodeckiBoundKey_finCut

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key keyBlock)
open QAlgorithms.Papers.Independent.Gap48.P42 (distillableKey)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.3: "Clearly, the
problem is reduced to drawing key from outcomes of measurement, from a state close to singlet,
which can be done, for example, by the protocol of Devetak and Winter [8]. As we have already
noted, this will draw γ states at the same rate as K_D when the corresponding classical protocol
is applied coherently."

There is `ε₀ > 0` such that for all finite shields `A′`, `B′` and every state `σ` on `A B A′ B′`
(one key qubit per party) whose `⟨00|·|11⟩` block `X` has `‖X‖₁ > 1/2 − ε₀`, the distillable
key of `σ` across `AA′ : BB′` is strictly positive. The paper uses the Devetak–Winter protocol
[8] for this and does not prove it.

**Formalization Note.** The threshold `ε₀` is chosen **before** the shield types: one
threshold for all shield dimensions, as the shields of `ρ′` in (12) grow with `l` and `n`.
Distillable key is read as `K_γ` (p.2), `Gap48.P42.distillableKey` of `finCut σ` (`ℝ≥0∞`);
`0 < K` means some positive rate is achievable. Shield types are in `Type` (universe 0). -/
theorem near_private_bit_key :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (S T : Type) [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
        (σ : Op (Key 2 × (S × T))), IsDensityMatrix σ →
        1 / 2 - ε₀ < traceNorm (keyBlock σ (0,0) (1,1)) →
        0 < distillableKey (finCut σ) := by sorry

end HorodeckiBoundKey
