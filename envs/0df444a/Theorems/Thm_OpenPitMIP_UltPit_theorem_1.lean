-- Prove2me | Theorems.Thm_OpenPitMIP_UltPit_theorem_1
-- name    : OpenPitMIP.UltPit.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:44.093599+00:00
-- url     : https://prove2.me/theorems/dfe94f81-9f8c-4a79-a893-1acbc88ef1de
-- title:
--   Theorem 1, p. 1431 — if G ≥ 0 and g ≥ 0, the pit limit of a minimal optimal PCPSP-C solution lies inside that of U-PIT
-- statement:
--   Consider an instance of the PCPSP-C, formulation (1)–(7), under the standing assumptions of §2.1 (clusters partition the blocks, $\prec$ induces a partial order on clusters, discount rate $r > 0$, weights $q_b \ge 0$), and suppose that
--   $$G \ge 0 \qquad\text{and}\qquad g \ge 0$$
--   entrywise. Fix either integrality condition, (10) or (11). Let $(x^*, y^*)$ be a minimal optimal solution of the PCPSP-C, and let $P^{OPT} = \{c \in \mathcal C : \sum_{t \in \mathcal T} x^*_{c,t} > 0\}$ be its pit limit. Let $x^U$ be the minimal optimal solution of the ultimate pit limit problem U-PIT (12)–(14), and $P^{U\text{-}PIT} = \{c : x^U_c > 0\}$ its pit limit. Then
--   $$P^{OPT} \subseteq P^{U\text{-}PIT}.$$
--
--   Consequently every cluster outside the ultimate pit limit can be removed from the PCPSP-C before it is solved, because some optimal solution does not use it. The ultimate pit limit is computed by a single maximum closure problem, independent of the time periods and resources.
--
--   **Formalization Note** The statement quantifies over every minimal optimal $(x^*, y^*)$ and every minimal optimal $x^U$; existence of either is not assumed. Minimality of $(x^*, y^*)$ is for the componentwise order on the pair $(x, y)$. At least one destination is assumed, so that $\max_d p_{b,d}$ exists. The objective uses the discounted values $p_{b,d}/(1+r)^t$ of §2.1.
-- source:
--   Oper. Res. 68(5), Theorem 1, p. 1431

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

namespace OpenPitMIP.UltPit

open PCPSPC

/-- Theorem 1, p. 1431: for an instance of the PCPSP-C with `G ≥ 0` and `g ≥ 0`, under either
integrality condition, the pit limit `P^OPT = {c : ∑_t x_{c,t} > 0}` of a minimal optimal
solution `(x, y)` is contained in the pit limit `P^{U-PIT}` of the minimal optimal solution of
U-PIT. -/
theorem theorem_1 {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [Nonempty D] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing)
    (hG : ∀ i b d t, 0 ≤ I.G i b d t) (hg : ∀ i, 0 ≤ I.g i)
    (κ : Integrality) (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ)
    (hopt : I.MinimalOptimal κ x y)
    (xU : C → ℝ) (hU : I.UPitMinimalOptimal xU) :
    pitLimit (fun c => ∑ t, x c t) ⊆ pitLimit xU := by sorry

end OpenPitMIP.UltPit
