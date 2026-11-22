-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_translation_continuous
-- name    : MasulloGRH.schwartzBruhat_translation_continuous
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:16.260848+00:00
-- url     : https://prove2.me/theorems/a1291673-9ed1-4848-8457-32fbcb04b128
-- title:
--   Proposition D.1.9.2 — the translation action $G\times\mathcal S(G)\to\mathcal S(G)$ is jointly continuous (second-countable $G$)
-- statement:
--   **Continuity of translation on the Schwartz–Bruhat space** (Proposition D.1.9.2).
--
--   Throughout, $G$ is a Hausdorff locally compact abelian group, written multiplicatively, and $\widehat G$ is its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$ with the compact-open topology). A closed subgroup $k\subseteq G$ is **good** if its annihilator $k^\perp=\{\chi\in\widehat G:\chi|_k=1\}$ is open and compactly generated in $\widehat G$ (then $k$ is compact). A pair $(\Gamma,k)$ of subgroups is **structural** if $\Gamma$ is open and compactly generated, $k$ is good and $k\subseteq\Gamma$; then $\Gamma/k$ is an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ ($F$ finite). $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ is the Fréchet space of functions on $G$ that vanish outside $\Gamma$, are $k$-invariant, and induce a smooth rapidly decreasing function on $\Gamma/k$. The **Schwartz–Bruhat space** is
--   $$\mathcal S(G)=\bigcup_{(\Gamma,k)}\mathcal S(k,\Gamma)$$
--   with the locally convex inductive limit topology (the finest locally convex topology making all inclusions $\mathcal S(k,\Gamma)\to\mathcal S(G)$ continuous).
--
--   For $g\in G$ and a function $f$ on $G$ let $(\rho(g)f)(x)=f(g^{-1}x)$ be the left translate of $f$. Assume that $G$ is **second countable**.
--
--   **Statement.**
--
--   1. Translation preserves $\mathcal S(G)$: $\rho(g)f\in\mathcal S(G)$ for all $g\in G$ and $f\in\mathcal S(G)$.
--   2. The action map
--   $$\rho\colon G\times\mathcal S(G)\longrightarrow\mathcal S(G),\qquad(g,f)\longmapsto\rho(g)f,$$
--   is (jointly) continuous.
--   3. In particular the action is uniformly continuous over compact sets: for every compact $K\subseteq G$ and every neighbourhood $U$ of $0$ in $\mathcal S(G)$ there is a neighbourhood $V$ of $0$ in $\mathcal S(G)$ with $\rho(g)f\in U$ for all $g\in K$ and $f\in V$ (the translations by elements of $K$ are equicontinuous).
--
--   For $G=\mathbb R^m$ this is the continuity of $(c,f)\mapsto f(\cdot-c)$ on $\mathbb R^m\times\mathcal S(\mathbb R^m)$. Joint continuity makes $\mathcal S(G)$ a continuous representation of $G$; the source proves it in order to make its Lemma 4.3.3.1 and the corollaries of that lemma applicable.
--
--   **Formalization Note.** The statement asserts the existence of a map `ρ : G → SchwartzBruhat G → SchwartzBruhat G` with `ρ g f x = f (g⁻¹ * x)` (which encodes part 1 and determines `ρ`), continuity of `fun p : G × SchwartzBruhat G => ρ p.1 p.2` for the product topology, and part 3 with neighbourhood filters of `0`. Since $G$ is abelian and inversion is a homeomorphism, the same holds for the convention $f(gx)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 781, Proposition D.1.9.2

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_translation_continuous
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ ρ : G → SchwartzBruhat G → SchwartzBruhat G,
      (∀ (g : G) (f : SchwartzBruhat G) (x : G), ρ g f x = f (g⁻¹ * x)) ∧
      Continuous (fun p : G × SchwartzBruhat G => ρ p.1 p.2) ∧
      ∀ K : Set G, IsCompact K → ∀ U ∈ 𝓝 (0 : SchwartzBruhat G),
        ∃ V ∈ 𝓝 (0 : SchwartzBruhat G), ∀ g ∈ K, ∀ f ∈ V, ρ g f ∈ U := by sorry

end MasulloGRH
