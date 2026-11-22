-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_cosetIntegral_isOpenQuotientMap
-- name    : MasulloGRH.schwartzBruhat_cosetIntegral_isOpenQuotientMap
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T15:23:07.108583+00:00
-- url     : https://prove2.me/theorems/980d541f-665d-4c34-aeca-98d5022cdbce
-- title:
--   Theorem D.1.7.1(2) — for second-countable $G$ the coset-integration map $\Phi_H\colon\mathcal S(G)\to\mathcal S(G/H)$ is open, i.e. a topological quotient map
-- statement:
--   **The push-forward $\mathcal S(G)\to\mathcal S(G/H)$ is a topological quotient map** (Theorem D.1.7.1(2), second-countable case).
--
--   Throughout, $G$ is a Hausdorff locally compact abelian group, written multiplicatively, and $\widehat G$ is its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$ with the compact-open topology). A closed subgroup $k\subseteq G$ is **good** if its annihilator $k^\perp=\{\chi\in\widehat G:\chi|_k=1\}$ is open and compactly generated in $\widehat G$ (then $k$ is compact). A pair $(\Gamma,k)$ of subgroups is **structural** if $\Gamma$ is open and compactly generated, $k$ is good and $k\subseteq\Gamma$; then $\Gamma/k$ is an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ ($F$ finite). $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ is the Fréchet space of functions on $G$ that vanish outside $\Gamma$, are $k$-invariant, and induce a smooth rapidly decreasing function on $\Gamma/k$. The **Schwartz–Bruhat space** is
--   $$\mathcal S(G)=\bigcup_{(\Gamma,k)}\mathcal S(k,\Gamma)$$
--   with the locally convex inductive limit topology (the finest locally convex topology making all inclusions $\mathcal S(k,\Gamma)\to\mathcal S(G)$ continuous).
--
--   Let $G$ be **second countable**, let $H\subseteq G$ be a closed subgroup with a Haar measure $\mu_H$, and let
--   $$\Phi_H\colon\mathcal S(G)\longrightarrow\mathcal S(G/H),\qquad\Phi_H(f)(xH)=\int_H f(xh)\,d\mu_H(h),$$
--   be the continuous linear map given by integration over the cosets of $H$.
--
--   **Statement.** $\Phi_H$ is a topological quotient map: it is surjective, continuous and open. Equivalently, $\mathcal S(G/H)$ is isomorphic, as a topological vector space, to the quotient $\mathcal S(G)/\ker\Phi_H$.
--
--   Second countability enters because $\mathcal S(G)$ and $\mathcal S(G/H)$ are then LF-spaces (strict inductive limits of sequences of Fréchet spaces), to which the open mapping theorem applies. Openness means that $\mathcal S(G/H)$ carries the quotient topology of $\mathcal S(G)$: a linear map from $\mathcal S(G/H)$ to a topological vector space is continuous as soon as its composite with $\Phi_H$ is, and the continuous linear functionals on $\mathcal S(G/H)$ (the tempered distributions on $G/H$) correspond exactly to the tempered distributions on $G$ that vanish on $\ker\Phi_H$.
--
--   **Formalization Note.** The map is not constructed in the statement: for every continuous linear map `Φ : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ H)` satisfying `Φ f (x : G ⧸ H) = ∫ h : H, f (x * h) ∂μH` for all `f` and `x` (there is exactly one, by `MasulloGRH.schwartzBruhat_cosetIntegral`), the conclusion is Mathlib's `IsOpenQuotientMap Φ` (surjective, continuous and open). `μH` is a regular Haar measure on `H` for the Borel σ-algebra induced from `G`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 776–777, Theorem D.1.7.1(2); classical reference: A. Grothendieck, Topological Vector Spaces, Gordon and Breach, 1973, Ch. 4, §5, Theorem 2(a), p. 148 (open mapping theorem for LF-spaces, as cited in the source)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open MeasureTheory Topology

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_cosetIntegral_isOpenQuotientMap
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (Φ : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ H))
    (hΦ : ∀ (f : SchwartzBruhat G) (x : G),
      Φ f (x : G ⧸ H) = ∫ h : H, f (x * (h : G)) ∂μH) :
    IsOpenQuotientMap Φ := by sorry

end MasulloGRH
