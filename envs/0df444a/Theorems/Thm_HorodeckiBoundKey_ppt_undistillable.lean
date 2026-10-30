-- Prove2me | Theorems.Thm_HorodeckiBoundKey_ppt_undistillable
-- name    : HorodeckiBoundKey.ppt_undistillable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:30.752929+00:00
-- url     : https://prove2.me/theorems/b2bfdec4-fdd2-4adc-bbe4-ae25fb1cb234
-- title:
--   PPT states have zero distillable entanglement ([22])
-- statement:
--   Let $\rho$ be a state (positive semidefinite, trace one) on $\mathbb C^a\otimes\mathbb C^b$, shared by Alice (first factor) and Bob (second factor). If $\rho$ has positive partial transpose, $\rho^{\Gamma}\succeq 0$, then no pure entanglement can be distilled from it:
--   $$
--   E_D(\rho) = 0 .
--   $$
--   Here $E_D$ is the distillable entanglement: the supremum of rates $r$ such that, for every $\varepsilon,\delta>0$ and all large $n$, a deterministic finite LOCC protocol turns $\rho^{\otimes n}$ into a state within trace distance $\varepsilon$ of $m$ Bell pairs with $m/n\ge r-\delta$.
--
--   The paper invokes this fact for the state (11) ("the state has positive partial transpose (PPT) being therefore bound entangled [22]") and cites it from [22] (M., P. and R. Horodecki, PRL 80, 5239, 1998) without proof. It gives the clause $E_D = 0$ of the main result.
--
--   **Formalization Note** The partial transpose is taken on Alice's factor (`Entanglement.partialTransposeFirst`); its positivity is equivalent to that of Bob's partial transpose. For a key-and-shield state the PPT clause of the main result (`transposeBob`) is converted by the proved identity $\Gamma_A(\mathrm{finCut}\,\rho) = (\mathrm{finCut}\,\rho^{\Gamma_B})^{\mathsf T}$. $E_D$ is the published operational rate `Gap48.P42.bipartiteDistillable`, valued in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: the PPT state (11) → every finite bipartite PPT state; reason: [22] proves the claim for every state; it specializes to (11) through finCut and the transposeBob bridge
--   - encoding: PPT (partial transpose on Bob's side, as for (11)) → partial transpose on Alice's factor, Entanglement.partialTransposeFirst; reason: the two partial transposes differ by a full transpose, which preserves positivity
--   - encoding: E_D, "no pure entanglement can be distilled" (not defined formally in the paper) → Gap48.P42.bipartiteDistillable, the operational Bell-pair rate under deterministic finite adaptive LOCC, in ℝ≥0∞; reason: the standard operational definition; ℝ≥0∞ avoids junk values of real suprema
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.3 ("the state has positive partial transpose (PPT) being therefore bound entangled [22]")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Gap48.P42 (bipartiteDistillable)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.3, "the state has
positive partial transpose (PPT) being therefore bound entangled [22]": a state with positive
partial transpose has zero distillable entanglement. The paper cites this from [22]
(M. Horodecki, P. Horodecki, R. Horodecki, Phys. Rev. Lett. 80, 5239 (1998)) and does not prove
it. Stated for every finite bipartite state.

**Formalization Note.** A state on `Fin a × Fin b` (Alice × Bob). PPT is positivity of the
partial transpose on Alice's factor, `Entanglement.partialTransposeFirst`; it is equivalent to
positivity of the partial transpose on Bob's factor (the two differ by a full transpose). For a
state given on the `Key 2 × (S × T)` layout, `partialTransposeFirst (finCut ρ)` is the full
transpose of `finCut (transposeBob ρ)`. Distillable entanglement `E_D` is the operational
Bell-pair rate `Gap48.P42.bipartiteDistillable` under deterministic finite adaptive LOCC, with
vanishing full trace-norm error, as an `ℝ≥0∞` supremum. -/
theorem ppt_undistillable {a b : ℕ} (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hρ : IsDensityMatrix ρ) (hppt : (Entanglement.partialTransposeFirst ρ).PosSemidef) :
    bipartiteDistillable ρ = 0 := by sorry

end HorodeckiBoundKey
