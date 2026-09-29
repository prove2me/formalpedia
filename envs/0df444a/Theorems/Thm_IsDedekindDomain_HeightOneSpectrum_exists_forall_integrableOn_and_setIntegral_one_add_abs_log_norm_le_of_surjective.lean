-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_forall_integrableOn_and_setIntegral_one_add_abs_log_norm_le_of_surjective
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_forall_integrableOn_and_setIntegral_one_add_abs_log_norm_le_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/52b9cb12-d8a6-575f-a5b1-da104b635549
-- title:
--   Logarithmic mass of thin slabs in Kᵥ-vector spaces
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of its ring of integers $\mathcal{O}_K$, and $K_v$ the $v$-adic completion of $K$. Let $E$ be an additive commutative group carrying the structure of a finite-dimensional $K_v$-vector space, equipped with the module topology over $K_v$ and with a Borel measurable structure compatible with that topology, and let $\nu$ be an additive Haar measure on $E$. Let $\lambda : E \to K_v$ be a surjective $K_v$-linear map, and let $Z \subseteq E$ be compact. The assertion is that there exists a real constant $C \ge 0$ such that for every real $R$ with $0 < R \le 1$ two things hold: first, the function $z \mapsto 1 + \lvert \log \lVert \lambda z\rVert\rvert$ is integrable with respect to $\nu$ on the slab $Z \cap \{ z : \lVert \lambda z\rVert \le R\}$, the norm being the $v$-adic absolute value on $K_v$; and second, $$\int_{Z \cap \{\lVert \lambda z\rVert \le R\}} \bigl(1 + \lvert \log \lVert \lambda z\rVert \rvert\bigr)\, d\nu(z) \;\le\; C\,R\,(1 + \lvert \log R\rvert).$$ The constant $C$ is uniform in $R$ but may depend on $K$, $v$, $E$, $\nu$, $\lambda$ and $Z$.
--
--   This is the quantitative estimate controlling the contribution of a thin slab $\{\lVert\lambda z\rVert \le R\}$ inside a compact set to integrals with a logarithmic singularity along the hyperplane $\lambda = 0$; the Haar-measure scaling behaviour of the module of $K_v$ (identified with the $v$-adic norm) and the local integrability of $\log$ of that module enter as inputs. It is used in the estimates for semi-local weight integrals on automorphic forms, where the logarithm of a norm of a trace must be integrated over a compact region.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_forall_integrableOn_and_setIntegral_one_add_abs_log_norm_le_of_surjective.lean

import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.exists_forall_integrableOn_and_setIntegral_one_add_abs_log_norm_le_of_surjective
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (E : Type) [AddCommGroup E] [Module (v.adicCompletion K) E] [FiniteDimensional (v.adicCompletion K) E]
    [TopologicalSpace E] [IsModuleTopology (v.adicCompletion K) E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    (lam : E →ₗ[(v.adicCompletion K)] (v.adicCompletion K)) (hlam : Function.Surjective lam)
    (Z : Set E) (hZ : IsCompact Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → R ≤ 1 →
      IntegrableOn (fun z : E => 1 + |Real.log ‖lam z‖|) (Z ∩ {z | ‖lam z‖ ≤ R}) ν ∧
      ∫ z in Z ∩ {z | ‖lam z‖ ≤ R}, (1 + |Real.log ‖lam z‖|) ∂ν ≤ C * R * (1 + |Real.log R|) := by sorry
