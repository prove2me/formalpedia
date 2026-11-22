-- Prove2me | Theorems.Thm_MasulloGRH_isAbsoluteBasis_iff_summable_of_frechet_or_strictLF
-- name    : MasulloGRH.isAbsoluteBasis_iff_summable_of_frechet_or_strictLF
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:20.206882+00:00
-- url     : https://prove2.me/theorems/b759d3fe-1db9-4631-ab3f-bed448bc59bb
-- title:
--   Remark 4.1.2.5 — in Fréchet spaces and strict LF-spaces of nuclear Fréchet spaces a Schauder basis is absolute iff $\sum_m q(f_m(u)x_m)<\infty$ for all $u$ and $q$
-- statement:
--   **Remark 4.1.2.5 — the definitions of absolute bases of Jarchow and McArthur agree.** Let $E$ be a Hausdorff locally convex complex vector space and $(x_m)_{m\ge0}$ a Schauder basis of $E$ with continuous coefficient functionals $(f_m)_{m\ge0}$. Following Jarchow (Definition 4.1.2.1(3)), the basis is *absolute* if for every continuous seminorm $q$ on $E$ there is a continuous seminorm $q'$ on $E$ with
--   $$\sum_{m\ge0}q\big(f_m(u)\,x_m\big)\le q'(u)\qquad(u\in E);$$
--   following McArthur, it is absolute if
--   $$\sum_{m\ge0}q\big(f_m(u)\,x_m\big)<\infty\qquad\text{for every }u\in E\text{ and every continuous seminorm }q\text{ on }E.$$
--   If $E$ is a Fréchet space, or a strict inductive limit of a sequence of nuclear Fréchet spaces, then the two conditions are equivalent.
--
--   The remark makes the notion of absolute Schauder basis used throughout the paper unambiguous for its Fréchet and strict LF-spaces of $\theta$-functions.
--
--   **Formalization Note.** Jarchow's condition is the platform's `MasulloGRH.IsAbsoluteBasis` (which also records the summability of the series, so that `tsum` is meaningful); McArthur's condition is spelled out with `Summable`. Fréchet spaces and strict inductive limits of sequences of nuclear Fréchet spaces are the platform notions `IsFrechet` and `IsStrictLFOfNuclearFrechet`; the standing assumption that $E$ is a Hausdorff locally convex space is the hypothesis `IsHLCS E`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 160–161, Remark 4.1.2.5; classical reference: C. W. McArthur, Developments in Schauder basis theory, Bull. Amer. Math. Soc. 78 (1972), §9, p. 900, and H. Jarchow, Locally Convex Spaces, Teubner, 1981, Part II, Ch. 14, §14.7, (*), p. 314 (the two definitions compared, as cited by the paper)

import Definitions.Def_MasulloGRH_SchauderBases

open Filter Topology

set_option autoImplicit false

namespace MasulloGRH

theorem isAbsoluteBasis_iff_summable_of_frechet_or_strictLF
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f)
    (hspace : IsFrechet E ∨ IsStrictLFOfNuclearFrechet E) :
    IsAbsoluteBasis x f ↔
      ∀ q : Seminorm ℂ E, Continuous q → ∀ u : E, Summable (fun m => q (f m u • x m)) := by sorry

end MasulloGRH
