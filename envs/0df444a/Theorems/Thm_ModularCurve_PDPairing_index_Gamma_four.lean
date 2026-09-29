-- Prove2me | Theorems.Thm_ModularCurve_PDPairing_index_Gamma_four
-- name    : ModularCurve.PDPairing.index_Gamma_four
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/f9449160-8909-5ef3-a16b-566bca75da35
-- title:
--   The index of Γ(4) in SL₂(ℤ) is 48
-- statement:
--   The statement has no variables or hypotheses: it is a closed numerical assertion about the principal congruence subgroup of level $4$. Here `CongruenceSubgroup.Gamma 4` denotes the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those matrices whose entries reduce, modulo $4$, to the corresponding entries of the identity matrix, i.e. the kernel of reduction $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/4\mathbb{Z})$, and `Subgroup.index` denotes the index, that is the cardinality of the coset space, taken as a natural number (with the convention that it is $0$ when the coset space is infinite). The assertion is that this index equals $48$. Since reduction modulo $4$ is surjective onto $\mathrm{SL}_2(\mathbb{Z}/4\mathbb{Z})$ with kernel $\Gamma(4)$, the content is equivalently that $\lvert \mathrm{SL}_2(\mathbb{Z}/4\mathbb{Z}) \rvert = 48$; in particular the index is finite, so the statement also records that $\Gamma(4)$ has finite index.
--
--   This is the standard index computation for the principal congruence subgroup of level $4$, the special case $N = 4$ of the formula $[\mathrm{SL}_2(\mathbb{Z}) : \Gamma(N)] = N^3 \prod_{p \mid N} (1 - p^{-2})$. It is used in the construction of the pairing associated with a point of order dividing $4$, in [`ModularCurve.PDPairing.exists_forall_smul_eq_pairZ_and_perfect_mod_three`](thm.html#ModularCurve.PDPairing.exists_forall_smul_eq_pairZ_and_perfect_mod_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PDPairing_index_Gamma_four.lean

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.PDPairing.index_Gamma_four : (CongruenceSubgroup.Gamma 4).index = 48 := by sorry
