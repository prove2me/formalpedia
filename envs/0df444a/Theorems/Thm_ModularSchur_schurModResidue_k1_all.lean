-- Prove2me | Theorems.Thm_ModularSchur_schurModResidue_k1_all
-- name    : ModularSchur.schurModResidue_k1_all
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:52:45.75815+00:00
-- url     : https://prove2.me/theorems/822fd673-9a8f-47b3-ac07-ad8bad2cf461
-- title:
--   Complete one-colour formula for all $m \ge 2$ and $\ell \ge 2$
-- statement:
--   This theorem states the single-colour modular Schur number for every admissible pair, with no restriction relating the modulus and the number of summands.
--
--   For every $m \ge 2$ and every $\ell \ge 2$,
--
--   $$ \mathrm{schurModResidue}(m,1,\ell) = \begin{cases} \min\!\left(\ell - 1, \left\lfloor m/\ell \right\rfloor\right), & \ell \le m, \\ 0, & \ell > m \text{ and } \ell \equiv 1 \pmod m, \\ 1, & \ell > m \text{ and } \ell \not\equiv 1 \pmod m. \end{cases} $$
--
--   The first branch is the regime treated in the literature; the remaining two cover a modulus smaller than $\ell$, where the answer degenerates to whether the all-ones tuple is already fatal.
--
--   This is the single statement a consumer can quote for the one-colour case without checking which regime a given pair falls into, and it closes the single-colour question completely.
-- source:
--   Not stated in McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository -- this is a result of the Lean development only. Prior art: The paper states the one-colour formula only under the hypothesis $2 \le \ell \le m$ (Theorem 6.1) and nowhere treats the regime $m < \ell$; this statement is a result of the Lean development going beyond the paper. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/K1Theorem.lean#L315-L323

import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset Classical
variable {m ℓ : ℕ}

theorem ModularSchur.schurModResidue_k1_all (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    schurModResidue m 1 ℓ =
      if ℓ ≤ m then min (ℓ - 1) (m / ℓ) else if ℓ % m = 1 then 0 else 1 := by sorry
