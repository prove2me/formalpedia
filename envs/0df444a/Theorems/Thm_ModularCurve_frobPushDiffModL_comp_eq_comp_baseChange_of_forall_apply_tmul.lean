-- Prove2me | Theorems.Thm_ModularCurve_frobPushDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul
-- name    : ModularCurve.frobPushDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/b319d81a-7117-5e63-8302-ac71fa2bf868
-- title:
--   Frobenius push-forward of differentials commutes with base change
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $p \mid M$ but $p^2 \nmid M$, $H$ a subgroup of $(\mathbb{Z}/M)^\times$, and $S$ a set of natural numbers. Write $\Gamma$ for [`CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained by pushing forward along $\Gamma_0(M/p) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ the preimage, under the homomorphism $\Gamma_0(M/p) \to (\mathbb{Z}/(M/p))^\times$ sending $\gamma$ to its lower-right entry, of the image of $H$ under `ZMod.unitsMap` for $(M/p) \mid M$. Let $k$ be an algebraically closed field of characteristic $p$ and $K$ an algebraically closed $k$-algebra field, and let $F_k =$ `qExpFunctionFieldC k` $\Gamma$, $F_K =$ `qExpFunctionFieldC K` $\Gamma$ be the subfields of the Laurent series fields generated over $k$, resp. $K$, by the ratios $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ of integral $q$-expansions of modular forms of equal weight for $\Gamma$. Assume given a $K$-linear map $\Phi : K \otimes_k \Omega_{F_k/k} \to \Omega_{F_K/K}$ which is injective and satisfies $\Phi(c \otimes f\,Dg) = c \cdot (f'\,Dg')$ whenever $f', g' \in F_K$ have Laurent series the coefficientwise images of those of $f, g \in F_k$ under $k \to K$. Assume further that over $k$ and over $K$ there exists a linear endomorphism $C$ of the module of Kähler differentials with $\mathrm{diffQExp}(C\omega)$ equal to the $p$-decimation $n \mapsto (\text{coefficient } pn)$ of $\mathrm{diffQExp}(\omega)$ for all $\omega$. Then the chosen operators `frobPushDiffModL` satisfy $\mathcal{C}_K \circ \Phi = \Phi \circ (\mathrm{id}_K \otimes \mathcal{C}_k)$, the second map being the base change of $\mathcal{C}_k$ to $K$.
--
--   This is the $U_p$-type compatibility of the Frobenius push-forward (Cartier) operator on differentials of the modular curve of level $M/p$ with extension of the algebraically closed base field: since the operator is pinned by its effect $a_n \mapsto a_{pn}$ on $q$-expansions and $q$-expansions of differentials are injective ([`ModularCurve.diffQExp_qExpFunctionFieldC_injective`](thm.html#ModularCurve.diffQExp_qExpFunctionFieldC_injective)), it is determined by that recipe over both fields, and $q$-expansions commute with scalar extension. It feeds the corresponding statement for the full collection of operators, [`ModularCurve.genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul`](thm.html#ModularCurve.genDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobPushDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve KaehlerDifferential
open ModularCurve

theorem ModularCurve.frobPushDiffModL_comp_eq_comp_baseChange_of_forall_apply_tmul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K]
    (Φ : K ⊗[k] Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k] →ₗ[K]
        Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K])
    (hinj : Function.Injective Φ)
    (hΦ : (∀ (c : K) (f g : ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
          (f' g' : ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
          (f' : LaurentSeries K) = coeffMap (algebraMap k K) (f : LaurentSeries k) →
          (g' : LaurentSeries K) = coeffMap (algebraMap k K) (g : LaurentSeries k) →
          Φ (c ⊗ₜ[k] (f • D k ↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) g)) =
            c • (f' • D K ↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) g')))
    (hCk : ∃ C : Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k] →ₗ[k] Ω[↥(qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄k],
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; IsFrobPushDiff k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p C)
    (hCK : ∃ C : Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K] →ₗ[K] Ω[↥(qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))⁄K],
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; IsFrobPushDiff K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p C)
    (hp0 : NeZero p) :
    (frobPushDiffModL K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p) ∘ₗ Φ = Φ ∘ₗ (frobPushDiffModL k (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p).baseChange K := by sorry
