-- Prove2me | Theorems.Thm_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
-- name    : HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/b62fe485-eff2-5567-b3f7-6e82ad03f4b6
-- title:
--   Norm and absolute value under L⊗_K Kᵥ≅prod_{w∣ v}L_w
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, i.e. a finite place of $K$; write $K_v$ for `v.adicCompletion K`. Write $v.\mathrm{Extension}\,\mathcal{O}_L$ for the subtype of height-one primes $w$ of $\mathcal{O}_L$ with $w$ lying under $v$ (i.e. $w.\mathrm{under}\,\mathcal{O}_K = v$), and for such a $w$ let $L_w$ be `w.1.adicCompletion L`. Let $e =$ `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v` be the $L$-algebra isomorphism $L\otimes_K K_v \xrightarrow{\sim} \prod_{w\mid v} L_w$ obtained from the bijectivity of the base change of the family of semialgebra maps to the completions. The theorem asserts three statements simultaneously: (1) for every $x\in L\otimes_K K_v$, the $K_v$-algebra norm of $x$ equals the finite product, over $w$ above $v$, of the $K_v$-algebra norms of the components $e(x)_w$; (2) for every $w$ above $v$ and every $y\in L_w$, the norm $\|\,\cdot\,\|$ of the $K_v$-algebra norm of $y$ equals $\|y\|$; and (3) for every $x\in L\otimes_K K_v$, $\|\mathrm{N}_{(L\otimes_K K_v)/K_v}(x)\| = \prod_{w\mid v}\|e(x)_w\|$, the products being `finprod`s over the subtype of extensions of $v$.
--
--   This is the standard compatibility of the norm with the semi-local decomposition $L\otimes_K K_v\cong\prod_{w\mid v}L_w$, together with the fact that the local norm $\mathrm{N}_{L_w/K_v}$ preserves the normalised absolute values, so that the absolute value of the global-at-$v$ norm is the product of the local absolute values. It is used in the automorphic-forms part of the development, in the estimates and integrality computations over semi-local integral sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (∀ x : L ⊗[K] v.adicCompletion K,
      Algebra.norm (v.adicCompletion K) x =
        ∏ᶠ w : v.Extension (𝓞 L),
          Algebra.norm (v.adicCompletion K)
            (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w)) ∧
    (∀ (w : v.Extension (𝓞 L)) (y : w.1.adicCompletion L),
      ‖Algebra.norm (v.adicCompletion K) y‖ = ‖y‖) ∧
    (∀ x : L ⊗[K] v.adicCompletion K,
      ‖Algebra.norm (v.adicCompletion K) x‖ =
        ∏ᶠ w : v.Extension (𝓞 L), ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w‖) := by sorry
