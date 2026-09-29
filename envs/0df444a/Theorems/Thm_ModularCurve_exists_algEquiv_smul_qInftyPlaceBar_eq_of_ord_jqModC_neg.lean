-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg
-- name    : ModularCurve.exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/fa23ab44-c93c-509b-b453-bc9c78dd6c60
-- title:
--   Poles of j lie in the orbit of the q-adic place
-- statement:
--   Let $K$ be a field, $N$ a nonzero natural number which is squarefree and whose image in $K$ is nonzero. Write $F =$ `modularFunctionFieldFullC K N` for the intermediate field of $K \subseteq \mathrm{LaurentSeries}\,K$ generated over $K$ by the set of series $\mathrm{qExpand}\,K\,d\,(\mathrm{jqModC}\,K)$ for nonzero $d \mid N$, where $\mathrm{jqModC}\,K = q^{-1}\cdot\iota(E_4^3\,\eta^{-24})$ is the $q$-expansion of $j$ with coefficients in $K$ and $\mathrm{qExpand}\,K\,d$ is the ring homomorphism substituting $q \mapsto q^{d}$ (reindexing a Hahn series along multiplication by $d$). Assume the hypothesis $h$: some element of $F$ has Laurent-series order exactly $-1$. Let $P$ be a place of $F$ over $K$ in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), that is a valuation subring of $F$ containing $K$, different from $F$ itself, and a principal ideal ring, and assume that $P.\mathrm{ord}$ of the element $\mathrm{jqModC}\,K$ of $F$ is negative, i.e. $j$ has a pole at $P$. The conclusion asserts the existence of a $K$-algebra automorphism $\sigma$ of $F$ such that, first, for every nonzero $d \mid N$ there is a nonzero $d' \mid N$ with $\sigma(\mathrm{qExpand}\,K\,d\,(\mathrm{jqModC}\,K)) = \mathrm{qExpand}\,K\,d'\,(\mathrm{jqModC}\,K)$ (so $\sigma$ maps each of the chosen generators to another such generator; bijectivity of $d \mapsto d'$ is not part of the assertion), and, second, $P = \sigma \cdot \mathrm{qInftyPlaceBar}\,K\,F\,h$, the translate under $\sigma$ of the place whose valuation subring is $\{f \in F : \mathrm{ord}_q(f) \ge 0\}$.
--
--   This is the statement that the poles of $j$ on the full modular function field of squarefree level $N$ are exhausted by the orbit of the standard $q$-adic (cuspidal) place under the Atkin–Lehner type automorphisms permuting the generators $j(q^d)$, $d \mid N$. It is used in the identification of the Frobenius action on places of the geometric level structure, in [`ModularCurve.CharPModel.frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg`](thm.html#ModularCurve.CharPModel.frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg.lean

import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg (K : Type*) [Field K]
    (N : ℕ) [NeZero N] (hsq : Squarefree N) (hNK : (N : K) ≠ 0)
    (h : ∃ j : modularFunctionFieldFullC K N, (qSeriesBar K (modularFunctionFieldFullC K N) j).order = -1)
    (P : Place K (modularFunctionFieldFullC K N))
    (hpole : P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) < 0) :
    ∃ σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N,
      (∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N), ∃ (d' : ℕ) (_ : NeZero d') (hd' : d' ∣ N),
          σ ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ = ⟨qExpand K d' (jqModC K), jqModCd_mem_full K N hd'⟩)
        ∧ P = σ • qInftyPlaceBar K (modularFunctionFieldFullC K N) h := by sorry
