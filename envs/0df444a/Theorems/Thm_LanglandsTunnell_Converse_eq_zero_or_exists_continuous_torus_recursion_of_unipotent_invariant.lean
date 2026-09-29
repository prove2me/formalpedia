-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant
-- name    : LanglandsTunnell.Converse.eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/f9005e51-8bab-538b-baf4-beff4cdd44d5
-- title:
--   Torus recursions for a unipotent-invariant Hecke eigenfunction
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}$, let $\Pi$ be a Hecke eigensystem over $K$ with complex values (a level ideal, assumed nonzero, together with families $v \mapsto \Pi.a\,v$ and $v \mapsto \Pi.b\,v$ indexed by the finite places), let $S$ be a finite set of finite places and $N$ an ideal of $\mathcal{O}_K$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ be continuous and assume: $\varphi\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)g) = \varphi(g)$ for all $x \in \mathbb{A}$ and all $g$; $\varphi(\gamma g) = \varphi(g)$ for every $\gamma \in \mathrm{GL}_2(K)$ whose lower left entry vanishes, mapped into $\mathrm{GL}_2(\mathbb{A})$ entrywise; $\varphi(gu) = \varphi(g)$ for every $u$ in the intersection of the level-$N$ subgroup `levelOne` with the kernel `finiteAdelicGL2Subgroup` of the archimedean component map; for every finite place $v \notin S$, $\varphi$ is a Hecke coset eigenfunction at $v$ with eigenvalue $\Pi.a\,v$, i.e. there are $N(v)+1$ elements of the double coset of `heckeGen` $v$ modulo that level group which form a system of representatives for the left cosets it meets, injectively, and $\sum_i \varphi(g\,\mathrm{reps}_i) = (\Pi.a\,v)\,\varphi(g)$ for all $g$; and the scalar matrix with entry $\det(\mathtt{heckeGen}\ v)$ acts on $\varphi$ by $N(v)^{-1}\,\Pi.b\,v$, where $N(v)$ is the absolute norm of $v$ viewed in $\mathbb{C}$. Then either $\varphi$ vanishes identically, or there exist a finite set $S_1$ of finite places and a continuous $\psi : \mathbb{A}^\times \times \mathbb{A}^\times \to \mathbb{C}$ with $\psi(1,1) \neq 0$, invariant under translation of either argument by the image of $K^\times$, and such that for every $v \notin S_1$ and all $t_1, t_2 \in \mathbb{A}^\times$, with $\varpi_v = \mathtt{uniformizerIdele}\ v$, one has $N(v)\,\psi(\varpi_v t_1, t_2) + \psi(t_1, \varpi_v t_2) = (\Pi.a\,v)\,\psi(t_1,t_2)$ and $\psi(\varpi_v t_1, \varpi_v t_2) = N(v)^{-1}(\Pi.b\,v)\,\psi(t_1,t_2)$.
--
--   This is the passage from a unipotent-invariant Hecke eigenfunction on $\mathrm{GL}_2(\mathbb{A})$ to its restriction to the diagonal torus, on which the unramified Hecke operators become the two classical recursions in a uniformizer at each good place. It feeds the analysis of the degenerate (Eisenstein) alternative in the converse direction of the Langlands–Tunnell argument, being cited by [`LanglandsTunnell.Converse.eq_zero_or_exists_agreesAwayFromFinite_eisensteinTableOf_of_unipotent_invariant`](thm.html#LanglandsTunnell.Converse.eq_zero_or_exists_agreesAwayFromFinite_eisensteinTableOf_of_unipotent_invariant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant.lean

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.SmoothCusp

theorem LanglandsTunnell.Converse.eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant
    (K : Type) [Field K] [NumberField K] (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (ϕ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous ϕ)
    (hunip : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), ϕ (unipotentGL2 x * g) = ϕ g)
    (hborel : ∀ γ ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, ϕ (globalPoints (𝓞 K) K γ * g) = ϕ g)
    (hlevel : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      ϕ (g * u) = ϕ g)
    (heigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v ϕ (Pi.a v))
    (hcentralEigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
      ϕ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g)
        = (HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ϕ g) :
    (∀ g : AdelicGL2 (𝓞 K) K, ϕ g = 0) ∨
      ∃ (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (ψ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ),
        Continuous ψ ∧ ψ (1, 1) ≠ 0 ∧
        (∀ (γ₁ γ₂ : Kˣ) (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ),
          ψ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) γ₁ * t₁,
              Units.map (algebraMap K (AdeleRing (𝓞 K) K)) γ₂ * t₂) = ψ (t₁, t₂)) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₁ → ∀ t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ,
          HeckeEigensystem.cNorm v * ψ (uniformizerIdele K v * t₁, t₂) + ψ (t₁, uniformizerIdele K v * t₂)
            = Pi.a v * ψ (t₁, t₂)) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₁ → ∀ t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ,
          ψ (uniformizerIdele K v * t₁, uniformizerIdele K v * t₂)
            = (HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ψ (t₁, t₂)) := by sorry
