-- Prove2me | Theorems.Thm_ModularCurve_qExpand_jq_mem_adjoin_of_primes_of_ne
-- name    : ModularCurve.qExpand_jq_mem_adjoin_of_primes_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/f6f1ecc3-53f9-5654-a3e8-23c240577558
-- title:
--   j(qᵈ) lies in ℚ(j(q^{dℓ}),j(q^{dℓ'}),j(q^{dℓℓ'}))
-- statement:
--   Let $d,\ell,\ell'$ be non-zero natural numbers with $\ell$ and $\ell'$ prime and $\ell \neq \ell'$. Here `jq` is the Laurent series over $\mathbb{Q}$ given by $q^{-1}$ times the power series `jNumQ`, the image under $\mathbb{Z} \to \mathbb{Q}$ of the integral power series `jNum`; thus `jq` is the $q$-expansion of the modular invariant $j$, written $j(q)$. For a non-zero natural number $n$, `qExpand ℚ n` is the ring endomorphism of $\mathbb{Q}$-Laurent series obtained by re-indexing the Hahn-series support along multiplication by $n$ on $\mathbb{Z}$, i.e. the substitution $q \mapsto q^{n}$; so `qExpand ℚ n jq` is $j(q^{n})$. The assertion is that $j(q^{d})$ belongs to the intermediate field of the field of Laurent series over $\mathbb{Q}$ generated over $\mathbb{Q}$ by the three elements $j(q^{d\ell})$, $j(q^{d\ell'})$ and $j(q^{d\ell\ell'})$, the adjunction being taken in the sense of `IntermediateField.adjoin` and therefore closed under inverses as well as under the ring operations.
--
--   This is the field-theoretic separation statement behind the classical fact that $j(q^{d})$ is the unique common root of the modular equations $\Phi_{\ell}(X, j(q^{d\ell}))$ and $\Phi_{\ell'}(X, j(q^{d\ell'}))$ for distinct primes $\ell \neq \ell'$, the extra generator $j(q^{d\ell\ell'})$ serving to distinguish the spurious roots. It is used in establishing that the images of the relevant Hecke-type operators generate the whole field, in [`ModularCurve.heckeBetaRoof_adjoin_range_union_eq_top`](thm.html#ModularCurve.heckeBetaRoof_adjoin_range_union_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpand_jq_mem_adjoin_of_primes_of_ne.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.qExpand_jq_mem_adjoin_of_primes_of_ne
    (d ℓ ℓ' : ℕ) [NeZero d] [NeZero ℓ] [NeZero ℓ']
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    qExpand ℚ d jq ∈ IntermediateField.adjoin ℚ
      {qExpand ℚ (d * ℓ) jq, qExpand ℚ (d * ℓ') jq, qExpand ℚ (d * ℓ * ℓ') jq} := by sorry
