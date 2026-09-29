-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_isHaarMeasure_map_eq_prod_localAt
-- name    : LanglandsTunnell.RankinSelberg.exists_isHaarMeasure_map_eq_prod_localAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/5890a450-52be-51c6-af3f-da37402bc6ef
-- title:
--   Haar splitting of finite-adelic GL₂ at one place
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a point of the height one spectrum of $\mathcal{O}_{\mathbb{Q}}$, and write $G$ for `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean component map on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$, with the adelic matrix group carrying its Borel structure; assume $G$ second countable. Let `localAt ℚ v` denote the homomorphism from $\mathrm{GL}_2$ of the adeles to $\mathrm{GL}_2(\mathbb{Q}_v)$ obtained by passing to the finite adeles and then to the $v$-component. Let $\iota : \mathrm{GL}_2(\mathbb{Q}_v) \to G$ be a continuous group homomorphism which is a section of `localAt ℚ v` restricted to $G$, so that the $v$-component of $\iota(x)$ is $x$ for all $x$, and which is central relative to the fibre, i.e. $\iota(x)$ commutes with every $k \in G$ whose $v$-component is $1$. Let $\mu$ be a Haar measure on $G$. Then, with $\mathrm{GL}_2(\mathbb{Q}_v)$ given its Borel structure, for every Haar measure $\mu_v$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ there is a Haar measure $\mu'$ on the kernel of `localAt ℚ v` composed with the inclusion of $G$ such that the pushforward of $\mu$ along $g \mapsto (\mathrm{localAt}_v(g),\ g \cdot \iota(\mathrm{localAt}_v(g))^{-1})$ equals the product of $\mu_v$ with the pushforward of $\mu'$ along the inclusion of that kernel into $G$.
--
--   This is the decomposition of a Haar measure on the finite-adelic $\mathrm{GL}_2$ as a product of a Haar measure at the place $v$ and a Haar measure on the subgroup trivial at $v$, available once a continuous section $\iota$ with the stated commutation property is given. It underlies the factorisation of finite-adelic Rankin–Selberg integrals into a local factor at $v$ and a complementary integral, and is used in the results expressing such an integral via the local Euler polynomial at $v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_isHaarMeasure_map_eq_prod_localAt.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.RankinSelberg.exists_isHaarMeasure_map_eq_prod_localAt
    (v : HeightOneSpectrum (𝓞 ℚ)) [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (ι : GL (Fin 2) (v.adicCompletion ℚ) →* finiteAdelicGL2Subgroup ℚ) (hι_cont : Continuous ι)
    (hι : ∀ x : GL (Fin 2) (v.adicCompletion ℚ), localAt ℚ v (ι x : AdelicGL2 (𝓞 ℚ) ℚ) = x)
    (hcomm : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (k : finiteAdelicGL2Subgroup ℚ),
      localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 → ι x * k = k * ι x)
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure] :
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
    ∀ (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μv.IsHaarMeasure],
      ∃ μ' : Measure ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker,
        μ'.IsHaarMeasure ∧
          Measure.map
              (fun g : finiteAdelicGL2Subgroup ℚ =>
                (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ), g * (ι (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹))
              μ =
            μv.prod (Measure.map Subtype.val μ') := by sorry
