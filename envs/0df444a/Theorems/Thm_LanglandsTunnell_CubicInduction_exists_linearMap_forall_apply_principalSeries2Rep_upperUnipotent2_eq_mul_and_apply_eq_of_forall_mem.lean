-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
-- name    : LanglandsTunnell.CubicInduction.exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/7815969b-1d47-5741-a40a-5ae04dc4cfb3
-- title:
--   Extension of ψ-Whittaker functionals on the principal series
-- statement:
--   Let $p$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the associated adic completion, and let $G = \mathrm{GL}_2(F)$. Fix a pair $\chi = (\chi_0,\chi_1)$ of monoid homomorphisms $F^\times \to \mathbb{C}^\times$ and an additive character $\psi \colon F \to \mathbb{C}$, i.e. a homomorphism from the additive group of $F$ to the multiplicative monoid of $\mathbb{C}$; no continuity or non-triviality is assumed of $\psi$. Let $I(\chi)$ be the complex subspace of functions $f \colon G \to \mathbb{C}$ that are locally constant, satisfy $f(n(x)g) = f(g)$ for all $x \in F$, $g \in G$, where $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$, and satisfy $f(\mathrm{diag}(a_0,a_1)\,g) = \chi_0(a_0)\chi_1(a_1)\,\sqrt{\|a_0\|/\|a_1\|}\;f(g)$ for all $a_0,a_1 \in F^\times$ and $g \in G$; the group acts on $I(\chi)$ by right translation, $g$ acting by $f \mapsto (h \mapsto f(hg))$. Let $U \subseteq I(\chi)$ be a complex subspace stable under right translation by every $n(x)$, $x \in F$, and let $\ell \colon U \to \mathbb{C}$ be a linear form with $\ell(n(x)\cdot u) = \psi(x)\,\ell(u)$ for all $x \in F$ and $u \in U$. Then there exists a linear form $L \colon I(\chi) \to \mathbb{C}$ with $L(n(x)\cdot f) = \psi(x)\,L(f)$ for all $x \in F$ and all $f \in I(\chi)$, and with $L(u) = \ell(u)$ for every $u \in U$.
--
--   This is the extension property of $\psi$-Whittaker functionals on the normalised principal series of $\mathrm{GL}_2(F)$, equivalently the injectivity of the map of twisted coinvariants $U_{N,\psi} \to I(\chi)_{N,\psi}$ for the unipotent radical $N \cong F$ of the Borel subgroup. It is used in the local analysis of the cubic induction, both in the computation of Jacquet integrals against flat sections and in the vanishing criterion for Whittaker functionals on subrepresentations of the principal series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ)
    (U : Submodule ℂ ↥(principalSeries2 p χ))
    (hU : ∀ (x : p.adicCompletion ℚ), ∀ u ∈ U, principalSeries2Rep χ (upperUnipotent2 p x) u ∈ U)
    (ℓ : ↥U →ₗ[ℂ] ℂ)
    (hℓ : ∀ (x : p.adicCompletion ℚ) (u : ↥U),
      ℓ ⟨principalSeries2Rep χ (upperUnipotent2 p x) u, hU x u u.2⟩ = ψ x * ℓ u) :
    ∃ L : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ,
      (∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p χ)),
        L (principalSeries2Rep χ (upperUnipotent2 p x) f) = ψ x * L f) ∧
      ∀ u : ↥U, L (u : ↥(principalSeries2 p χ)) = ℓ u := by sorry
