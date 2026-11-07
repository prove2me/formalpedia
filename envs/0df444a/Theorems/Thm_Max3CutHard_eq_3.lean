-- Prove2me | Theorems.Thm_Max3CutHard_eq_3
-- name    : Max3CutHard.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:49.851933+00:00
-- url     : https://prove2.me/theorems/96cd02a9-4145-4f99-ac46-626e8cbc83e7
-- title:
--   Eq. (3) — the values of the family $(2E,N,N)$
-- statement:
--   For the family $(I_0,I_1,I_2)=(2E,N,N)$, every $x\in\mathbb Z_3^3$ and every type $t\in\mathbb Z_3$,
--
--   $$V_t(x)=\beta_t+2\big([s(x)=t]+[s(x)=-t]\big),\qquad \beta_0=32,\ \beta_1=\beta_2=9.$$
--
--   This formula turns the soundness analysis into the count $\mathrm{val}_\Phi(\sigma)+\mathrm{val}_\Phi(-\sigma)$ (the negation trick).
--
--   Differences from the source:
--   - encoding: V_t(x) without a globals argument → gval x y for every colouring y of the isolated globals; reason: the globals carry no edges
--   - encoding: colours [k] and ℤ₃, primaries p1, p2, p3, tuples (x1, x2, x3) → Fin k and ZMod 3 (= Fin 3), indices 0, 1, 2; reason: Lean convention; same instances
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Proof of Theorem 1.1, Eq. (3), p.6

import Mathlib
import Definitions.Def_Max3CutHard_family0
import Definitions.Def_Max3CutHard_Gadget_gval
import Definitions.Def_Max3CutHard_sumX
import Definitions.Def_Max3CutHard_betaT

namespace Max3CutHard

/-- **Eq. (3).** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Proof of Theorem 1.1, Eq. (3), p.6: "Use the family `(2E, N, N)`, i.e. `E`
with all weights doubled for type 0 and `N` for types 1, 2. By Lemma 3.1, for every `x` and every
type `t`, `V_t(x) = β_t + 2([s(x) = t] + [s(x) = −t])`, `β0 = 32`, `β1 = β2 = 9`. (3)"

**Formalization Note.** Stated for every colouring `y` of the (isolated) globals. -/
theorem eq_3 : ∀ (t : ZMod 3) (x : Fin 3 → ZMod 3) (y : Fin 3 → Fin 3),
    (family0 t).gval x y =
      betaT t + 2 * ((if sumX x = t then 1 else 0) + (if sumX x = -t then 1 else 0)) := by sorry

end Max3CutHard
