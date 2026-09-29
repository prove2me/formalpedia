-- Prove2me | Theorems.Thm_LocalNewvector_exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep
-- name    : LocalNewvector.exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/58a9a5a5-d9df-50c0-a7aa-b43ddcae84c1
-- title:
--   Submodules of an isotypic sum are sums of images of V
-- statement:
--   Let $q$ be a prime. Let $V$ be a complex vector space carrying an additive action of $\mathrm{GL}_2(\mathbb{Q}_q)$ whose operators commute with the complex scalars, and suppose $V$ is irreducible in the sense of the project's predicate [`LocalNewvector.IsIrreducibleGLRep`](def/LocalNewvector_ConductorDatum.html#L102): $V$ contains a nonzero vector, and every $\mathbb{C}$-submodule $W \subseteq V$ with $g \cdot v \in W$ for all $g \in \mathrm{GL}_2(\mathbb{Q}_q)$ and all $v \in W$ is either $\bot$ or $\top$. Let $N$ be a second complex vector space with an additive $\mathrm{GL}_2(\mathbb{Q}_q)$-action commuting with the complex scalars. Let $\iota$ be a type and let $L : N \to (\iota \to_{\mathrm{f}} V)$ be an injective $\mathbb{C}$-linear map into the finitely supported functions $\iota \to V$, with $L(x \cdot n) = x \cdot L(n)$ for every $x \in \mathrm{GL}_2(\mathbb{Q}_q)$ and $n \in N$, the action on the finitely supported functions being the coordinatewise one. Then there exist a type $\kappa$ and a family $f : \kappa \to (V \to_{\mathbb{C}} N)$ of $\mathbb{C}$-linear maps such that $f_i(x \cdot v) = x \cdot f_i(v)$ for all $i \in \kappa$, $x \in \mathrm{GL}_2(\mathbb{Q}_q)$, $v \in V$, and such that the supremum of the submodules $\mathrm{range}(f_i)$, $i \in \kappa$, is all of $N$. No injectivity, independence or directness is asserted of the family $(f_i)$, and no continuity or smoothness is assumed of any of the actions.
--
--   This is the structure theorem for subrepresentations of a $V$-isotypic direct sum, in the form needed for abstract complex representations of $\mathrm{GL}_2(\mathbb{Q}_q)$: a representation that embeds equivariantly into a direct sum of copies of an irreducible $V$ is spanned by equivariant images of $V$. It is used in the construction of the automorphic representation attached to a newform, namely by [`AutomorphicForm.exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre`](thm.html#AutomorphicForm.exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre) and by [`CuspForm.IsNewform.isIrreducibleGLRep_of_linearMap_range_eq_span_padic_smul_self`](thm.html#CuspForm.IsNewform.isIrreducibleGLRep_of_linearMap_range_eq_span_padic_smul_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep.lean

import Definitions.Def_LocalNewvector_ConductorDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LocalNewvector.exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep
    (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (N : Type) [AddCommGroup N] [Module ℂ N] [DistribMulAction (GL (Fin 2) ℚ_[q]) N]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ N]
    (hV : LocalNewvector.IsIrreducibleGLRep q V)
    (ι : Type) (L : N →ₗ[ℂ] (ι →₀ V)) (hL : Function.Injective L)
    (hLx : ∀ (x : GL (Fin 2) ℚ_[q]) (n : N), L (x • n) = x • L n) :
    ∃ (κ : Type) (f : κ → (V →ₗ[ℂ] N)),
      (∀ (i : κ) (x : GL (Fin 2) ℚ_[q]) (v : V), f i (x • v) = x • f i v) ∧
        ⨆ i : κ, LinearMap.range (f i) = ⊤ := by sorry
