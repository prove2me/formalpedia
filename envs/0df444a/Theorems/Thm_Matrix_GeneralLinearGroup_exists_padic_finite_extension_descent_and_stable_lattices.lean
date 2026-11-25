-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_exists_padic_finite_extension_descent_and_stable_lattices
-- name    : Matrix.GeneralLinearGroup.exists_padic_finite_extension_descent_and_stable_lattices
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:54:58.391473+00:00
-- url     : https://prove2.me/theorems/f1fa2142-7f45-4fce-847c-3d4912e51150
-- title:
--   Descent of an l-adic representation of a finitely generated group to a finite extension E of Q_l, with its stable subspaces and stable O_E-lattices
-- statement:
--   Let $\ell$ be a prime, $\overline{\mathbb{Q}}_\ell$ an algebraic closure of $\mathbb{Q}_\ell$, $\Gamma$ a finitely generated group and
--
--   $$\rho : \Gamma \to \mathrm{GL}_r(\overline{\mathbb{Q}}_\ell)$$
--
--   a homomorphism. Let $W_1, \dots, W_m \subseteq \overline{\mathbb{Q}}_\ell^{\,r}$ be subspaces stable under $\rho(\Gamma)$ (for example the terms of a composition series). Then there are a finite extension $E/\mathbb{Q}_\ell$ inside $\overline{\mathbb{Q}}_\ell$ and a homomorphism $\rho_E : \Gamma \to \mathrm{GL}_r(E)$ such that:
--
--   1. **$\rho$ is defined over $E$**: $\rho(g)$ is the image of $\rho_E(g)$ under the inclusion $E \subseteq \overline{\mathbb{Q}}_\ell$, for every $g \in \Gamma$.
--   2. **The stable subspaces descend to $E$**: each $W_k$ is spanned over $\overline{\mathbb{Q}}_\ell$ by its $E$-rational points $W_k \cap E^r$.
--   3. **Stable lattices** (when $\Gamma$ is finite): for each $k$ there is a finitely generated $\mathcal{O}_E$-submodule $\Lambda_k \subseteq E^r$, where $\mathcal{O}_E$ is the integral closure of $\mathbb{Z}_\ell$ in $E$, which is stable under $\rho_E(\Gamma)$ and whose $E$-span is exactly $W_k \cap E^r$.
--
--   This is the standard reduction of $\overline{\mathbb{Q}}_\ell$-coefficients to a finite coefficient field $E_\lambda$ with ring of integers $\mathcal{O}_\lambda$: the representation, a composition series and so its Jordan-Holder constituents are all realised over one finite extension of $\mathbb{Q}_\ell$, and (for a finite group) each piece carries an integral structure.
--
--   **Formalization Note**: $\overline{\mathbb{Q}}_\ell$ is `AlgebraicClosure ℚ_[l]`, $E$ is an `IntermediateField ℚ_[l] (AlgebraicClosure ℚ_[l])` with `FiniteDimensional ℚ_[l] E`, and $\mathrm{GL}_r$ is `Matrix.GeneralLinearGroup (Fin r)`. Finite generation is the instance `[Group.FG Γ]`; stability of `W k` is `Matrix.mulVec (ρ g) v ∈ W k` for `v ∈ W k`. Part 1 says `(ρE g).map (algebraMap E _) = ρ g` entrywise. In part 2 the $E$-rational points are `W k ∩ Set.range (fun v i => (v i : AlgebraicClosure ℚ_[l]))` (vectors with all coordinates in $E$). Part 3 is stated under the extra hypothesis `Finite Γ`; $\mathcal{O}_E$ is `integralClosure ℤ_[l] E` and $\Lambda$ is a `Submodule (integralClosure ℤ_[l] E) (Fin r → E)`; the last clause `v ∈ Submodule.span E Λ ↔ (fun i => (v i : AlgebraicClosure ℚ_[l])) ∈ W k` says that the $E$-span of $\Lambda$ is exactly $W_k \cap E^r$ (so $\Lambda \subseteq W_k$ and $\Lambda$ spans it). For infinite finitely generated $\Gamma$ a stable finitely generated lattice need not exist (an element of infinite order may act with eigenvalue $\ell$), so part 3 genuinely needs finiteness. Example: for the trivial group, $r = 2$ and $W_1 = \overline{\mathbb{Q}}_\ell \cdot (1, \sqrt{\ell})$, part 2 forces $\sqrt{\ell} \in E$ once $W_1$ must be spanned by $E$-points.
-- source:
--   J.-P. Serre, Linear Representations of Finite Groups, Section 15.2 (stable lattices); P. Deligne, La conjecture de Weil II, Publ. Math. IHES 52 (1980) (l-adic coefficients realised over finite extensions E_lambda of Q_l); standard descent of finitely many matrix entries to a finite subextension

import Mathlib

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.exists_padic_finite_extension_descent_and_stable_lattices
    (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [Group.FG Γ] (r m : ℕ)
    (ρ : Γ →* Matrix.GeneralLinearGroup (Fin r) (AlgebraicClosure ℚ_[l]))
    (W : Fin m → Submodule (AlgebraicClosure ℚ_[l]) (Fin r → AlgebraicClosure ℚ_[l]))
    (hW : ∀ (k : Fin m) (g : Γ) (v : Fin r → AlgebraicClosure ℚ_[l]), v ∈ W k →
      Matrix.mulVec (ρ g : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ_[l])) v ∈ W k) :
    ∃ (E : IntermediateField ℚ_[l] (AlgebraicClosure ℚ_[l]))
      (ρE : Γ →* Matrix.GeneralLinearGroup (Fin r) E),
      FiniteDimensional ℚ_[l] E ∧
      (∀ g : Γ, (ρE g : Matrix (Fin r) (Fin r) E).map (algebraMap E (AlgebraicClosure ℚ_[l])) =
        (ρ g : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ_[l]))) ∧
      ∀ k : Fin m,
        Submodule.span (AlgebraicClosure ℚ_[l])
            ((W k : Set (Fin r → AlgebraicClosure ℚ_[l])) ∩
              Set.range (fun (v : Fin r → E) (i : Fin r) => (v i : AlgebraicClosure ℚ_[l]))) = W k ∧
          (Finite Γ → ∃ Λ : Submodule (integralClosure ℤ_[l] E) (Fin r → E), Λ.FG ∧
            (∀ (g : Γ) (v : Fin r → E), v ∈ Λ →
              Matrix.mulVec (ρE g : Matrix (Fin r) (Fin r) E) v ∈ Λ) ∧
            ∀ v : Fin r → E, v ∈ Submodule.span E (Λ : Set (Fin r → E)) ↔
              (fun i : Fin r => (v i : AlgebraicClosure ℚ_[l])) ∈ W k) := by
  sorry
