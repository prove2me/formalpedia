-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_oneParameterDeriv
-- name    : MasulloGRH.schwartzBruhat_oneParameterDeriv
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:02.065459+00:00
-- url     : https://prove2.me/theorems/1355c28c-456f-4248-9f28-6bb986064c75
-- title:
--   Lemma D.1.6.7(1) — the derivative $\partial_a$ along a one-parameter subgroup $a\colon\mathbb R\to G$ is a continuous linear endomorphism of $\mathcal S(G)$
-- statement:
--   **Invariant first-order differential operators on the Schwartz–Bruhat space** (Definition D.1.6.5, Lemma D.1.6.6 and Lemma D.1.6.7(1)).
--
--   Throughout, $G$ is a Hausdorff locally compact abelian group, written multiplicatively, and $\widehat G$ is its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$ with the compact-open topology). A closed subgroup $k\subseteq G$ is **good** if its annihilator $k^\perp=\{\chi\in\widehat G:\chi|_k=1\}$ is open and compactly generated in $\widehat G$ (then $k$ is compact). A pair $(\Gamma,k)$ of subgroups is **structural** if $\Gamma$ is open and compactly generated, $k$ is good and $k\subseteq\Gamma$; then $\Gamma/k$ is an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ ($F$ finite). $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ is the Fréchet space of functions on $G$ that vanish outside $\Gamma$, are $k$-invariant, and induce a smooth rapidly decreasing function on $\Gamma/k$. The **Schwartz–Bruhat space** is
--   $$\mathcal S(G)=\bigcup_{(\Gamma,k)}\mathcal S(k,\Gamma)$$
--   with the locally convex inductive limit topology (the finest locally convex topology making all inclusions $\mathcal S(k,\Gamma)\to\mathcal S(G)$ continuous).
--
--   A **one-parameter subgroup** of $G$ is a continuous homomorphism $a\colon\mathbb R\to G$; these form the set $\mathcal L(G)=\mathrm{Hom}_{\mathrm{cont}}(\mathbb R,G)$ (Definition D.1.6.1). The **invariant differential operator** of $a$ is
--   $$(\partial_a f)(g)=\lim_{t\to0}\frac{f(g\,a(t))-f(g)}{t}=\frac{d}{dt}\Big|_{t=0}f\big(g\,a(t)\big),\qquad g\in G .$$
--
--   **Statement.** Let $a\in\mathcal L(G)$. For every $f\in\mathcal S(G)$ and every $g\in G$ the function $t\mapsto f(g\,a(t))$ is differentiable at $t=0$, the function $\partial_a f$ belongs to $\mathcal S(G)$, and
--   $$\partial_a\colon\mathcal S(G)\longrightarrow\mathcal S(G)$$
--   is a continuous linear map.
--
--   On a stage $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ the operator $\partial_a$ is the constant-coefficient first-order differential operator of the elementary abelian Lie group $\Gamma/k\cong\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ in the direction of the one-parameter subgroup $t\mapsto a(t)k$ (the image of $a$ is connected, so it lies in every open subgroup $\Gamma$). The operators $\partial_a$ commute with translations and with each other, and they generate the algebra $\mathrm{Diff}(G)$ of invariant differential operators of $G$ (Definition D.1.6.8); for $G=\mathbb R^n$ they are the directional derivatives.
--
--   **Formalization Note.** A one-parameter subgroup is a continuous monoid homomorphism `a : Multiplicative ℝ →ₜ* G`, so $a(t)$ is `a (Multiplicative.ofAdd t)`. The statement asserts the existence of a continuous linear map `D : SchwartzBruhat G →L[ℂ] SchwartzBruhat G` with `HasDerivAt (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) (D f g) 0` for all `f` and `g`; this determines `D` uniquely.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 766–767, Definition D.1.6.5, Lemma D.1.6.6 and Lemma D.1.6.7(1)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_oneParameterDeriv
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (a : Multiplicative ℝ →ₜ* G) :
    ∃ D : SchwartzBruhat G →L[ℂ] SchwartzBruhat G,
      ∀ (f : SchwartzBruhat G) (g : G),
        HasDerivAt (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) (D f g) 0 := by sorry

end MasulloGRH
