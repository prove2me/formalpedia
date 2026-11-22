-- Prove2me | Theorems.Thm_MasulloGRH_isShrinkingBasis_of_semiReflexive
-- name    : MasulloGRH.isShrinkingBasis_of_semiReflexive
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:04.72675+00:00
-- url     : https://prove2.me/theorems/203754e5-8914-4afb-a50e-8b51e19c3f81
-- title:
--   Every Schauder basis of a complete semi-reflexive locally convex space is shrinking: the coefficient functionals form a Schauder basis of $E'_\beta$
-- statement:
--   **Schauder bases of semi-reflexive spaces are shrinking.** Let $E$ be a complete Hausdorff locally convex topological $\mathbb C$-vector space which is *semi-reflexive*, i.e. every continuous linear functional on the strong dual $E'_\beta$ is the evaluation at a unique point of $E$:
--   $$\forall\,\Phi\in(E'_\beta)'\ \ \exists!\,u\in E:\qquad \Phi(g)=g(u)\quad\text{for all } g\in E'.$$
--   Let $(x_m)_{m\ge0}$ be a Schauder basis of $E$ with coefficient functionals $(f_m)_{m\ge0}\subset E'$. Then $(f_m)_{m\ge0}$ is a Schauder basis of the strong dual $E'_\beta$ whose coefficient functionals are the evaluations at the $x_m$: $f_m(x_n)=\delta_{mn}$ and, for every $\varphi\in E'$,
--   $$\varphi=\sum_{m\ge0}\varphi(x_m)\,f_m=\lim_{k\to\infty}\sum_{m=0}^{k}\varphi(x_m)\,f_m\qquad\text{in }E'_\beta,$$
--   i.e. uniformly on the bounded subsets of $E$. In other words, every Schauder basis of $E$ is *shrinking*.
--
--   This is the theorem recalled at the opening of §10.2 (p. 438), where it is combined with the fact that a Schauder basis and its coefficient functionals form a Markushevich basis, so that $\{(x_m,f_m)\}_{m\ge0}$ is a Markushevich basis for the duality $\langle E,E'\rangle$. The paper also invokes the same result of Jarchow in the proof of Lemma 4.1.2.4 (p. 160), for complete barrelled reflexive spaces and, when the space is nuclear, for its strong dual, and in Corollary 7.3.1.8 (p. 350) for its orbital Schauder bases on spaces of adelic theta functions.
--
--   **Formalization Note.** Uses the platform definitions `MasulloGRH.IsHLCS`, `MasulloGRH.IsCompleteTVS`, `MasulloGRH.IsSchauderBasis` and `MasulloGRH.IsShrinkingBasis` (which unfolds to `IsDualSchauderBasis`: biorthogonality plus convergence of $\sum_{m\le k}\varphi(x_m)f_m$ to $\varphi$ in Mathlib's strong topology on `StrongDual ℂ E`, the topology of uniform convergence on von Neumann bounded subsets of $E$). Semi-reflexivity is written inline exactly as in the platform theorem `MasulloGRH.strongDual_barrelledSpace_of_semiReflexive` (it is the first half of the platform's `MasulloGRH.IsReflexive`). Completeness is assumed because the paper assumes it at this place.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 438, §10.2 (opening paragraph); classical reference: H. Jarchow, Locally Convex Spaces, B. G. Teubner, Stuttgart, 1981, Part II, Ch. 14, §14.5, Thm. 1(a), p. 302 (as cited by the paper)

import Definitions.Def_MasulloGRH_SchauderBases

set_option autoImplicit false

namespace MasulloGRH

theorem isShrinkingBasis_of_semiReflexive
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (hc : IsCompleteTVS E)
    (hsr : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! u : E, ∀ g : StrongDual ℂ E, φ g = g u)
    (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) :
    IsShrinkingBasis x f := by sorry

end MasulloGRH
