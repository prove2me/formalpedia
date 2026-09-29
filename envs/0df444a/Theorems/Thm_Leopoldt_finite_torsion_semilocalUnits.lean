-- Prove2me | Theorems.Thm_Leopoldt_finite_torsion_semilocalUnits
-- name    : Leopoldt.finite_torsion_semilocalUnits
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:43:01.380044+00:00
-- url     : https://prove2.me/theorems/7d6e1baf-11a0-4311-b977-736a32836dfd
-- title:
--   The torsion subgroup of the semilocal units $U$ is finite
-- statement:
--   Let $K$ be a number field, $p$ a prime, and
--   $$U=\prod_{\mathfrak p\mid p}\mathcal O_{\mathfrak p}^\times$$
--   the group of semilocal units at $p$ (the platform's `SemilocalUnits p K`). Then the torsion subgroup
--   $$U_{\mathrm{tors}}=\{u\in U:\ u^n=1\text{ for some }n\ge 1\}=\prod_{\mathfrak p\mid p}\mu(K_{\mathfrak p})$$
--   is **finite**; equivalently each completion $K_{\mathfrak p}$ contains only finitely many roots of unity.
--
--   This finiteness is what makes $\mathbb{Z}_p$-ranks of subgroups of $U$ well behaved: up to a finite group, $U$ is its principal part, a finitely generated $\mathbb{Z}_p$-module.
-- source:
--   J. Neukirch, Algebraic Number Theory, Ch. II §5, Prop. 5.7 ($\mathcal O^\times\cong\mu_{q-1}\times U^{(1)}$, $U^{(1)}\cong\mu_{p^a}\times\mathbb Z_p^d$; in particular $\mu(K_\mathfrak p)$ is finite); P. Mihăilescu, arXiv:1105.4544, §1.1

import Definitions.Def_LeopoldtDefect

namespace Leopoldt

theorem finite_torsion_semilocalUnits (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [NumberField K] : Finite (CommGroup.torsion (SemilocalUnits p K)) := by sorry

end Leopoldt
