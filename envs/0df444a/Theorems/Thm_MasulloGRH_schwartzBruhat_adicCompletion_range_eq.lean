-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_adicCompletion_range_eq
-- name    : MasulloGRH.schwartzBruhat_adicCompletion_range_eq
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:39:25.421009+00:00
-- url     : https://prove2.me/theorems/a093b5fd-b807-4c8c-9175-43fbd8da1fa2
-- title:
--   §2.1.2.1 — $\mathcal S(F_v)=C_c^\infty(F_v)$: the Schwartz–Bruhat functions on a non-archimedean completion are the locally constant functions with compact support
-- statement:
--   **Schwartz–Bruhat functions on a non-archimedean local field** (§2.1.2.1 and Example 2.1.2.6 of the source).
--
--   Let $F$ be a number field, $v$ a finite place of $F$ and $F_v$ the completion of $F$ at $v$, a totally disconnected locally compact field with ring of integers $\mathcal O_{F_v}$ and uniformizer $\pi_v$. Let $\mathcal S(F_v)$ be the Schwartz–Bruhat space of the additive group of $F_v$ in the sense of Bruhat: the union, over all pairs $(\Gamma,k)$ of an open compactly generated subgroup $\Gamma\subset F_v$ and a good compact subgroup $k\subset\Gamma$, of the spaces of functions supported in $\Gamma$, invariant under $k$, whose induced function on the elementary abelian Lie group $\Gamma/k$ is smooth and of rapid decay.
--
--   Then, as a space of functions on $F_v$,
--   $$\mathcal S(F_v)=C_c^\infty(F_v)=\{h\colon F_v\to\mathbb C\ :\ h\text{ is locally constant and has compact support}\}.$$
--
--   Equivalently, every $f\in\mathcal S(F_v)$ is a finite linear combination $f=\sum_i c_i\,1_{a_i+\pi_v^{N_i}\mathcal O_{F_v}}$ of indicator functions of balls, and every such combination is in $\mathcal S(F_v)$ (eq. (2.1.2.1) of the source).
--
--   This is the classical definition of the space of test functions on a $p$-adic field used in Tate's thesis; it is the local factor of the restricted tensor product description of $\mathcal S(\mathbb A_F)$, and the source uses it for all computations with local zeta integrals. Note that the analogous identity fails for the multiplicative group $F_v^\times$ (Remark 2.1.2.1 of the source).
--
--   **Formalization Note.** The left-hand side is the set of underlying functions $x\mapsto f(x)$ of the elements $f$ of the platform space `MasulloGRH.SchwartzBruhat (Multiplicative (v.adicCompletion F))` (groups are written multiplicatively there, so the additive group of $F_v$ is `Multiplicative (v.adicCompletion F)`); the right-hand side uses Mathlib's `IsLocallyConstant` and `HasCompactSupport`. Only the equality of function spaces is stated; the topology of $\mathcal S(F_v)$ (the finest locally convex topology) is the platform theorem `MasulloGRH.schwartz_local_nonarchimedean_structure`. Example 2.1.2.6 of the source derives (2.1.2.1) from a decomposition of "every open subset" into finitely many balls, which holds for compact open subsets only; the statement here does not depend on that wording.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 63, §2.1.2.1 (identity $C_c^\infty(F_v)=\mathcal S(F_v)$), and p. 65, Example 2.1.2.6, eq. (2.1.2.1); classical reference cited there (pp. 62–63): F. Bruhat, Distributions sur un groupe localement compact et applications à l'étude des représentations des groupes $p$-adiques, Bulletin de la S.M.F., tome 89 (1961), §1 and §9

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_adicCompletion_range_eq
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Set.range (fun (f : SchwartzBruhat (Multiplicative (v.adicCompletion F)))
        (x : v.adicCompletion F) => f (Multiplicative.ofAdd x)) =
      {h : v.adicCompletion F → ℂ | IsLocallyConstant h ∧ HasCompactSupport h} := by sorry

end MasulloGRH
