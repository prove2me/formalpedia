-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isRightInvariant_foldr_archDeriv_sum_translate
-- name    : LanglandsTunnell.CubicInduction.isRightInvariant_foldr_archDeriv_sum_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/18d682d5-ead5-5a8a-ba2d-a3c7f51751c8
-- title:
--   Finite-adelic invariance of derivative words of translate combinations
-- statement:
--   Let $f$ be a complex-valued function on $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$, let $S$ be a finite set of height-one primes of $\mathcal{O}_{\mathbb{Q}}$, and assume: (i) for every prime $p \notin S$, $f(g\,u) = f(g)$ for all adelic $g$ and all $u$ in the image under `localToAdelic3` of the subgroup `localMaximalCompact3` of $\mathrm{GL}_3$ of the $v$-adic completion, consisting of those matrices all of whose entries, and all of whose inverse's entries, have valuation $\le 1$; and (ii) at every finite place $v$ there is an open subgroup $U_v \le \mathrm{GL}_3$ of the completion at $v$ with $f(g \cdot \iota_v(k)) = f(g)$ for all $k \in U_v$ and all $g$. Let $n \in \mathbb{N}$, $c : \mathrm{Fin}\,n \to \mathbb{C}$, $t : \mathrm{Fin}\,n \to \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, and let $w$ be a list of pairs $(i,j) \in \mathrm{Fin}\,3 \times \mathrm{Fin}\,3$. Apply to $x \mapsto \sum_i c_i\, f(x\,t_i)$ the operators `WhittakerBlock.archDeriv` $i\,j$ indexed by the entries of $w$, folded from the right (so the head of $w$ is applied outermost), where $\mathrm{archDeriv}\,i\,j\,\varphi(g)$ is the derivative at $s = 0$ of $s \mapsto \varphi\bigl(g \cdot \mathrm{archRealLift3}(1 + s E_{ij})\bigr)$. The conclusion is that the resulting function again has both properties: there is a finite set $S'$ of height-one primes such that it is right invariant under the image of `localMaximalCompact3` at every $p \notin S'$, and at every finite place $v$ it is right invariant under some open subgroup of $\mathrm{GL}_3$ of the completion at $v$.
--
--   This is the statement that finite-adelic regularity — sphericality outside a finite set of primes together with smoothness (invariance under an open subgroup) at each finite place — is inherited by archimedean derivative words applied to finite linear combinations of right translates. It is used in [`LanglandsTunnell.CubicInduction.exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant`](thm.html#LanglandsTunnell.CubicInduction.exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant), where such derivative words of translates of an automorphic form on $\mathrm{GL}_3$ must be known to remain admissible inputs for the Whittaker estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isRightInvariant_foldr_archDeriv_sum_translate.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

theorem
LanglandsTunnell.CubicInduction.isRightInvariant_foldr_archDeriv_sum_translate
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (w : List (Fin 3 × Fin 3)) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ p, p ∉ S' → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w
              (g * localToAdelic3 v k) =
            List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w g) := by sorry
