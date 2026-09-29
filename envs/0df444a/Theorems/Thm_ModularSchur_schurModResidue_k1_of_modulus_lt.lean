-- Prove2me | Theorems.Thm_ModularSchur_schurModResidue_k1_of_modulus_lt
-- name    : ModularSchur.schurModResidue_k1_of_modulus_lt
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:50:12.674632+00:00
-- url     : https://prove2.me/theorems/0b3934fb-6922-436a-8520-a40b03b1fe94
-- title:
--   One colour with $m < \ell$: the value is $0$ or $1$ by $\ell \bmod m$
-- statement:
--   This theorem settles the single-colour value in the regime the paper's one-colour theorem excludes, namely a modulus smaller than the number of summands.
--
--   For every $m \ge 2$ and every $\ell$ with $m < \ell$,
--
--   $$ \mathrm{schurModResidue}(m,1,\ell) = \begin{cases} 0, & \ell \equiv 1 \pmod m, \\ 1, & \text{otherwise.} \end{cases} $$
--
--   When $\ell \equiv 1 \pmod m$ the all-ones $\ell$-tuple sums to $\overline{1}$, so even the interval $\{\overline{1}\}$ fails and no nonempty interval can be coloured; otherwise that singleton interval is safe, and the length cannot be pushed to $2$.
--
--   Together with the $2 \le \ell \le m$ case this completes the single-colour picture over all $\ell \ge 2$, leaving no gap in the one-colour regime.
-- source:
--   Not stated in McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository -- this is a result of the Lean development only. Prior art: The paper states the one-colour formula only under the hypothesis $2 \le \ell \le m$ (Theorem 6.1) and nowhere treats the regime $m < \ell$; this statement is a result of the Lean development going beyond the paper. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/K1Theorem.lean#L293-L313

import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset Classical
variable {m ℓ : ℕ}

theorem ModularSchur.schurModResidue_k1_of_modulus_lt (m ℓ : ℕ) (hm : 2 ≤ m) (hml : m < ℓ) :
    schurModResidue m 1 ℓ = if ℓ % m = 1 then 0 else 1 := by sorry
