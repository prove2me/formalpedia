-- Prove2me | Theorems.Thm_MasulloGRH_exists_fundamentalDomain_normOneIdeles
-- name    : MasulloGRH.exists_fundamentalDomain_normOneIdeles
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:44.037517+00:00
-- url     : https://prove2.me/theorems/8c771770-fbd8-4598-a20a-4fbf3e4fa374
-- title:
--   Proposition A.2.3.10 (existence form) — a relatively compact strict fundamental domain with non-empty interior for $F^\times$ acting on the norm-one ideles
-- statement:
--   **Existence of a relatively compact fundamental domain for $F^\times$ on the norm-one ideles** (Proposition A.2.3.10 of the source, in a form that does not refer to the explicit domain $E_F^1$).
--
--   Let $F$ be a number field, $\mathbb I_F=\mathrm{GL}_1(\mathbb A_F)$ its idele group with the idele topology, $|g|_F=\prod_v|g_v|_v$ the idelic norm, and $\mathbb I_F^1=\{g\in\mathbb I_F:\ |g|_F=1\}$ the group of norm-one ideles with the induced topology; $F^\times$ is embedded diagonally in $\mathbb I_F^1$ (product formula). Then there exists a subset $E\subset\mathbb I_F^1$ such that:
--
--   1. the closure $\overline E$ of $E$ in $\mathbb I_F^1$ is compact;
--   2. the interior of $E$ in $\mathbb I_F^1$ is non-empty;
--   3. $E$ is a strict fundamental domain for $F^\times$: every $g\in\mathbb I_F^1$ can be written as $g=\xi e$ with $\xi\in F^\times$, $e\in E$, for exactly one $\xi$; equivalently $F^\times E=\mathbb I_F^1$ and $\xi E\cap E=\varnothing$ for all $\xi\in F^\times$, $\xi\neq1$;
--   4. the translates are locally finite: for every compact $K\subset\mathbb I_F^1$ only finitely many $\xi\in F^\times$ satisfy $\xi\overline E\cap K\neq\varnothing$.
--
--   The source proves this for the explicit domain $E=E_F^1=\bigcup_ig_i(E_0\times\widehat{\mathcal O}_F^\times)$ of Tate's thesis (Definition A.2.3.6; the explicit statements are `MasulloGRH.tateIdeleDomain_relCompact_and_interior_nonempty`, `MasulloGRH.tateIdeleDomain_existsUnique_principal_mul` and `MasulloGRH.tateIdeleDomain_finite_translates`). The existence form is the one needed in most applications: it implies that $F^\times$ is discrete and cocompact in $\mathbb I_F^1$ (compactness of $C_F^1=\mathbb I_F^1/F^\times$) and provides a domain on which integrals over $C_F^1$ can be unfolded; unlike a merely measurable fundamental domain, $E$ has compact closure, non-empty interior and locally finite translates.
--
--   **Formalization Note.** $\mathbb I_F$ is `MasulloGRH.IdeleGroup F = (AdeleRing (𝓞 F) F)ˣ` with the units topology, $|\cdot|_F$ is `MasulloGRH.ideleNorm`, $\mathbb I_F^1$ is the subtype `{g // ideleNorm g = 1}` with the subspace topology, and the diagonal embedding is `MasulloGRH.principalIdele`. This statement is weaker than the source's proposition, which concerns the specific set $E_F^1$; it needs no new definition.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 552, Proposition A.2.3.10 (existence form; the general notion of fundamental domain is recalled at the head of §A.2.3, p. 548); general references given by the paper for §A.2 (p. 545): D. Ramakrishnan, R.J. Valenza, Fourier Analysis on Number Fields, Springer, Ch. 5, §5.1; J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, §4.1, §4.3

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm

open NumberField IsDedekindDomain
open scoped NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem exists_fundamentalDomain_normOneIdeles (F : Type*) [Field F] [NumberField F] :
    ∃ E : Set {g : IdeleGroup F // ideleNorm g = 1},
      IsCompact (closure E) ∧ (interior E).Nonempty ∧
      (∀ g : {g : IdeleGroup F // ideleNorm g = 1},
        ∃! ξ : Fˣ, ∃ e ∈ E, (g : IdeleGroup F) = principalIdele F ξ * (e : IdeleGroup F)) ∧
      ∀ K : Set {g : IdeleGroup F // ideleNorm g = 1}, IsCompact K →
        {ξ : Fˣ | ∃ e ∈ closure E, ∃ k ∈ K,
          (k : IdeleGroup F) = principalIdele F ξ * (e : IdeleGroup F)}.Finite := by sorry

end MasulloGRH
