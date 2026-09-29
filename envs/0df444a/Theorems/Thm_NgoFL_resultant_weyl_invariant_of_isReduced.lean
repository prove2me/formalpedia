-- Prove2me | Theorems.Thm_NgoFL_resultant_weyl_invariant_of_isReduced
-- name    : NgoFL.resultant_weyl_invariant_of_isReduced
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T17:43:13.834722+00:00
-- url     : https://prove2.me/theorems/de6e4a22-e218-42dc-950c-eefd644f4b4d
-- title:
--   Lemme 1.10.2 (reduced form): $\prod_{\alpha \in \Lambda} d\alpha$ is $W_H$-invariant
-- statement:
--   Let $\Phi$ be a **reduced** root system with Weyl group $W$, let $\Phi_H \subseteq \Phi$ be a closed
--   subsystem with Weyl group $W_H$, and choose a subset $\Lambda \subseteq \Phi - \Phi_H$ containing
--   exactly one root out of each pair $\{\alpha, -\alpha\}$ of opposite roots outside $\Phi_H$. Ngô's
--   resultant is
--
--   $$ R^G_H \;=\; \prod_{\alpha \in \Lambda} d\alpha , $$
--
--   a polynomial function on the Cartan which depends, a priori, on the choice of $\Lambda$.
--
--   The statement (Lemme 1.10.2) is that this function is invariant under $W_H$: for every $w \in W_H$
--   and every $x$ in the Cartan, $R^G_H(wx) = R^G_H(x)$. Since $W_H$ permutes $\Phi - \Phi_H$ but does
--   **not** preserve $\Lambda$, the product can only be recovered up to the sign $(-1)^{m(w)}$, where
--   $m(w)$ is the number of roots of $\Lambda$ that $w$ sends into $-\Lambda$; the content of the lemma
--   is that this sign is always $+1$. The lemma is what makes $R^G_H$ descend to a well-defined function
--   on the space of characteristic polynomials of $H$, and hence what makes the divisor
--   $\mathfrak{R}^G_H$ of 1.10.3 exist.
--
--   This is the corrected form of `NgoFL.resultant_weyl_invariant`, which omitted the reducedness
--   hypothesis and is false without it: in the non-reduced system $BC_1 = \{\pm\alpha, \pm 2\alpha\}$
--   with $\Phi_H = \{\pm 2\alpha\}$ and $\Lambda = \{\alpha\}$, the reflection $s_{2\alpha} = -1$ lies in
--   $W_H$ and changes the sign of $\prod_{\beta \in \Lambda} d\beta$. Reducedness is exactly what is
--   needed for Ngô's sign argument, and it holds for the root system of a split reductive group.
-- source:
--   Bao Chau Ngo, *Le lemme fondamental pour les algebres de Lie*, Publications mathematiques de l'IHES 111 (2010), 1-169, DOI 10.1007/s10240-010-0026-7, pp. 20-21, Lemme 1.10.2

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant

namespace NgoFL

theorem resultant_weyl_invariant_of_isReduced {ι M N : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] [Fintype ι] [DecidableEq ι] (P : RootPairing ι ℚ M N)
    [P.IsRootSystem] [P.IsReduced] (s L : Finset ι) (hs : IsClosedSubsystem P (s : Set ι))
    (hL : IsHalfSystem P sᶜ L) (w : N ≃ₗ[ℚ] N)
    (hw : w ∈ weylSubgroup P (s : Set ι)) (x : N) :
    resultant P L (w x) = resultant P L x := by sorry

end NgoFL
