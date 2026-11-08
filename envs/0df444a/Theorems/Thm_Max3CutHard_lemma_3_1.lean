-- Prove2me | Theorems.Thm_Max3CutHard_lemma_3_1
-- name    : Max3CutHard.lemma_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:48:08.428486+00:00
-- url     : https://prove2.me/theorems/8b651bb8-ce5f-49a1-a07c-ea45913bbcfe
-- title:
--   Lemma 3.1 — values of the E- and N-gadgets
-- statement:
--   **Lemma 3.1.** For all $x\in\mathbb Z_3^3$, with $s(x)=x_1+x_2+x_3$,
--
--   $$V_E(x)=\begin{cases}18 & s(x)=0,\\ 16&\text{otherwise,}\end{cases}\qquad V_N(x)=\begin{cases}11& s(x)\ne0,\\ 9&\text{otherwise.}\end{cases}$$
--
--   Here $V_E$ and $V_N$ are the gadget values of the E-gadget and the N-gadget (3 colours), the maximum of the cut weight over the colours of the auxiliary vertices with the primaries coloured $x$.
--
--   The lemma is the computation behind the family $(2E,N,N)$ and equation (3).
--
--   Differences from the source:
--   - encoding: V_E(x), V_N(x) without a globals argument (the gadgets do not use their globals) → gval x y for every colouring y of the isolated globals; reason: the globals carry no edges, so the value does not depend on y
--   - encoding: colours [k] and ℤ₃, primaries p1, p2, p3, tuples (x1, x2, x3) → Fin k and ZMod 3 (= Fin 3), indices 0, 1, 2; reason: Lean convention; same instances
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Lemma 3.1, p.5

import Mathlib
import Definitions.Def_Max3CutHard_gadgetE
import Definitions.Def_Max3CutHard_gadgetN
import Definitions.Def_Max3CutHard_Gadget_gval
import Definitions.Def_Max3CutHard_sumX

namespace Max3CutHard

/-- **Lemma 3.1.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Lemma 3.1, p.5: "For all `x ∈ ℤ₃^3`: `V_E(x) = 18` if `s(x) = 0` and
`V_E(x) = 16` otherwise; `V_N(x) = 11` if `s(x) ≠ 0` and `V_N(x) = 9` otherwise."

**Formalization Note.** `ℤ₃ = Fin 3` serves both as the tuple values and as the colours. The
gadgets do not use their globals (Section 3), so the value is stated for every colouring `y` of
the globals. -/
theorem lemma_3_1 : ∀ (x : Fin 3 → ZMod 3) (y : Fin 3 → Fin 3),
    gadgetE.gval x y = (if sumX x = 0 then 18 else 16) ∧
    gadgetN.gval x y = (if sumX x ≠ 0 then 11 else 9) := by sorry

end Max3CutHard
