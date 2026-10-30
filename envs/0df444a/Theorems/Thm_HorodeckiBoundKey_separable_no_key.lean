-- Prove2me | Theorems.Thm_HorodeckiBoundKey_separable_no_key
-- name    : HorodeckiBoundKey.separable_no_key
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:49.224932+00:00
-- url     : https://prove2.me/theorems/1978326a-bd91-4521-bc5e-b7cdd8e830e3
-- title:
--   Separable states have zero distillable key
-- statement:
--   Let $\rho$ be a matrix on $\mathbb C^a\otimes\mathbb C^b$ shared by Alice and Bob. If $\rho$ is a separable state, then
--   $$
--   K(\rho) = 0 .
--   $$
--
--   The paper does not state this separately. It follows from its Theorem 2, $K_D\le E_r^\infty$ (p.4, proof in [18]), since the relative entropy of entanglement vanishes on separable states, and it is what turns $K>0$ into entanglement in the summary "One can even have $K_D>0$ for bound entangled states" (p.4). It gives the clause "not separable" of the main result.
--
--   **Formalization Note** Separability is `IsSeparable`. $K$ is the operational private-dit rate `Gap48.P42.distillableKey`, valued in $[0,\infty]$. Theorem 2 itself is not posed in this mission.
--
--   Differences from the source:
--   - reading: the implicit claim that a state with K_D > 0 is entangled (consequence of Theorem 2, p.4) → every separable finite bipartite state has K = 0; reason: the consequence of K_D ≤ E_r^∞ with E_r = 0 on separable states, stated for every finite bipartite state as Theorem 2 is
--   - reading: distillable key K_D (key drawn by local operations and public communication; not defined formally in the paper) → K_γ, the operational private-dit rate Gap48.P42.distillableKey under deterministic finite adaptive LOCC (ℝ≥0∞); reason: p.2 identifies the two rates ("We thus have equality of the two rates", with "Clearly K_γ ≤ K_D") and the proof on p.3 distils γ states "at the same rate as K_D"; the mission uses this one key rate throughout
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.4 ("In summary, we have found that in general E_D ≤ K_D ≤ E_r^∞ ≤ E_c"), with Theorem 2, p.4, and p.1 ("states which require entanglement to create")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_HorodeckiBoundKey_IsSeparable

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Gap48.P42 (distillableKey)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.4 ("In summary, we
have found that in general E_D ≤ K_D ≤ E_r^∞ ≤ E_c"), with p.1 ("bound entangled states (states
which require entanglement to create …)"): a separable state has zero distillable key. The
paper does not state this separately; it is the consequence of Theorem 2 (`K_D ≤ E_r^∞`, p.4,
proved in [18]) with `E_r = 0` on separable states, and it is what makes a state with positive
key entangled. Theorem 2 itself is not posed in this mission. Stated for every finite bipartite
state.

**Formalization Note.** A matrix on `Fin a × Fin b` (Alice × Bob); separability is
`IsSeparable` (finite convex combination of product density matrices). Distillable key is read
as `K_γ` (p.2): the operational rate `Gap48.P42.distillableKey` of distilling private dits by
deterministic finite adaptive LOCC, with key dimension and shields free at every blocklength,
vanishing full trace-norm error, as an `ℝ≥0∞` supremum. -/
theorem separable_no_key {a b : ℕ} (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hsep : IsSeparable ρ) : distillableKey ρ = 0 := by sorry

end HorodeckiBoundKey
