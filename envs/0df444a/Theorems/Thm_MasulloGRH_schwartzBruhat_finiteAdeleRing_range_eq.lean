-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_finiteAdeleRing_range_eq
-- name    : MasulloGRH.schwartzBruhat_finiteAdeleRing_range_eq
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:39:26.311107+00:00
-- url     : https://prove2.me/theorems/2cb09dd6-2808-4b56-8490-ad5b8e01fe0f
-- title:
--   Example 2.1.3.1 — $\mathcal S(\mathbb A_F^f)$ is the space of locally constant functions with compact support on the finite adeles
-- statement:
--   **Schwartz–Bruhat functions on the finite adeles** (Example 2.1.3.1 and the proof of Lemma 2.1.3.2 of the source).
--
--   Let $F$ be a number field and $\mathbb A_F^f=\widehat{\prod}_{v<\infty}(F_v,\mathcal O_{F_v})$ its ring of finite adeles, a totally disconnected locally compact ring in which the compact open subgroups $N\widehat{\mathcal O}_F$ and $N^{-1}\widehat{\mathcal O}_F$ ($N\ge1$) form a neighbourhood base of $0$ and an exhaustion, respectively. Let $\mathcal S(\mathbb A_F^f)$ be the Schwartz–Bruhat space of the additive group of $\mathbb A_F^f$ in the sense of Bruhat (the union of the spaces $\mathcal S(\Gamma/k)$ over the structural pairs $(\Gamma,k)$).
--
--   Then, as a space of functions on $\mathbb A_F^f$,
--   $$\mathcal S(\mathbb A_F^f)=C_c^\infty(\mathbb A_F^f)=\{h\colon\mathbb A_F^f\to\mathbb C\ :\ h\text{ is locally constant and has compact support}\}.$$
--
--   Equivalently, $\mathcal S(\mathbb A_F^f)$ is spanned by the indicator functions $\prod_v1_{a_v+\pi_v^{N_v}\mathcal O_{F_v}}$ with $a_v=0$, $N_v=0$ for almost all $v$.
--
--   This is the non-archimedean factor in the decomposition $\mathcal S(\mathbb A_F)=\mathcal S(\mathbb A_{F,S_\infty})\otimes\mathcal S(\mathbb A_F^f)$ of Lemma 2.1.3.2 of the source, and the form in which adelic test functions are used in Tate's thesis.
--
--   **Formalization Note.** The left-hand side is the set of underlying functions of the elements of the platform space `MasulloGRH.SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))`; the right-hand side uses Mathlib's `IsLocallyConstant` and `HasCompactSupport`. Only the equality of function spaces is stated; the topological properties of $\mathcal S(\mathbb A_F^f)$ are the platform theorem `MasulloGRH.schwartz_adeles_structure`. The source states the identity for $F=\mathbb Q$ in Example 2.1.3.1 and uses it for general $F$ in the proof of Lemma 2.1.3.2.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 67, Example 2.1.3.1 ("$\mathcal S(\mathbf A^f_{\mathbf Q})$ agrees with the $\mathbf C$-vector space of all smooth compactly supported functions on $\mathbf A^f_{\mathbf Q}$"), with p. 63, §2.1.2.1, and pp. 69–70, proof of Lemma 2.1.3.2 (general $F$); classical reference cited there (p. 67, p. 69): F. Bruhat, Distributions sur un groupe localement compact et applications à l'étude des représentations des groupes $p$-adiques, Bulletin de la S.M.F., tome 89 (1961)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_finiteAdeleRing_range_eq
    (F : Type*) [Field F] [NumberField F] :
    Set.range (fun (f : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F)))
        (x : FiniteAdeleRing (𝓞 F) F) => f (Multiplicative.ofAdd x)) =
      {h : FiniteAdeleRing (𝓞 F) F → ℂ | IsLocallyConstant h ∧ HasCompactSupport h} := by sorry

end MasulloGRH
