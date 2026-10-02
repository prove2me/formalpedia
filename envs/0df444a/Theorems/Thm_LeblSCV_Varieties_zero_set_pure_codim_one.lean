-- Prove2me | Theorems.Thm_LeblSCV_Varieties_zero_set_pure_codim_one
-- name    : LeblSCV.Varieties.zero_set_pure_codim_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:13:47.368873+00:00
-- url     : https://prove2.me/theorems/79837716-0318-4bf3-b763-bc6a9c33e265
-- title:
--   Theorem 6.5.9 — the zero set of a holomorphic function is a hypervariety with dense regular part
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain (a nonempty connected open set) and let $f$ be holomorphic on $U$, with zero set $Z_f = \{ z \in U : f(z) = 0 \}$. Then at least one of the following holds:
--   1. $Z_f = \emptyset$;
--   2. $Z_f$ is a subvariety of $U$ of pure codimension $1$;
--   3. $Z_f = U$.
--
--   Furthermore, the set of regular points $(Z_f)_{\mathrm{reg}}$ is open in $Z_f$ and dense in $Z_f$:
--   $$(Z_f)_{\mathrm{reg}} = O \cap Z_f \text{ for some open } O, \qquad Z_f \subset \overline{(Z_f)_{\mathrm{reg}}}.$$
--
--   This restates Theorem 1.6.2 in the language of varieties; it is the prototype of a hypervariety.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; a domain is `IsOpen U ∧ IsConnected U` (Mathlib's `IsConnected` includes nonemptiness); holomorphic is `DifferentiableOn ℂ f U`. Codimension is computed in `ℤ`. "Open in $Z_f$" is the subspace topology, written with an ambient open set $O$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 187, Theorem 6.5.9

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsSubvariety
import Definitions.Def_LeblSCV_Varieties_regularPoints
import Definitions.Def_LeblSCV_Varieties_IsPureCodim

namespace LeblSCV.Varieties

/-- Lebl, Theorem 6.5.9: for a domain `U ⊆ ℂⁿ` and `f ∈ 𝒪(U)`, the zero set
`Z_f = U ∩ f⁻¹(0)` is empty, or a subvariety of `U` of pure codimension 1, or all of `U`;
furthermore `(Z_f)_reg` is open in `Z_f` and dense in `Z_f`. -/
theorem zero_set_pure_codim_one {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hUconn : IsConnected U) {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) :
    (U ∩ f ⁻¹' {0} = ∅ ∨
        (IsSubvariety U (U ∩ f ⁻¹' {0}) ∧ IsPureCodim (U ∩ f ⁻¹' {0}) 1) ∨
        U ∩ f ⁻¹' {0} = U) ∧
      (∃ O : Set (Fin n → ℂ), IsOpen O ∧
        regularPoints (U ∩ f ⁻¹' {0}) = O ∩ (U ∩ f ⁻¹' {0})) ∧
      U ∩ f ⁻¹' {0} ⊆ closure (regularPoints (U ∩ f ⁻¹' {0})) := by sorry

end LeblSCV.Varieties
