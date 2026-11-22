-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_hasCompactSupport_dense
-- name    : MasulloGRH.schwartzBruhat_hasCompactSupport_dense
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:10.05164+00:00
-- url     : https://prove2.me/theorems/2c09b805-f794-4e8d-980b-1970d05391d9
-- title:
--   §D.1.8 — compactly supported Schwartz–Bruhat functions are dense in $\mathcal S(G)$
-- statement:
--   **Density of the compactly supported functions in the Schwartz–Bruhat space** (§D.1.8, p. 777).
--
--   Throughout, $G$ is a Hausdorff locally compact abelian group, written multiplicatively, and $\widehat G$ is its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$ with the compact-open topology). A closed subgroup $k\subseteq G$ is **good** if its annihilator $k^\perp=\{\chi\in\widehat G:\chi|_k=1\}$ is open and compactly generated in $\widehat G$ (then $k$ is compact). A pair $(\Gamma,k)$ of subgroups is **structural** if $\Gamma$ is open and compactly generated, $k$ is good and $k\subseteq\Gamma$; then $\Gamma/k$ is an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ ($F$ finite). $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ is the Fréchet space of functions on $G$ that vanish outside $\Gamma$, are $k$-invariant, and induce a smooth rapidly decreasing function on $\Gamma/k$. The **Schwartz–Bruhat space** is
--   $$\mathcal S(G)=\bigcup_{(\Gamma,k)}\mathcal S(k,\Gamma)$$
--   with the locally convex inductive limit topology (the finest locally convex topology making all inclusions $\mathcal S(k,\Gamma)\to\mathcal S(G)$ continuous).
--
--   Let $\mathcal D(G)=C_c^\infty(G)$ be the space of compactly supported elements of $\mathcal S(G)$: the functions on $G$ that vanish outside some $\Gamma$, are $k$-invariant and induce a smooth compactly supported function on $\Gamma/k$, for some structural pair $(\Gamma,k)$ (Bruhat's test functions).
--
--   **Statement.** The set of $f\in\mathcal S(G)$ with compact support is dense in $\mathcal S(G)$.
--
--   Consequently the restriction map on continuous duals $\mathcal S(G)'\to\mathcal D(G)'$ is injective: a tempered distribution on $G$ (a continuous linear functional on $\mathcal S(G)$) is determined by its values on compactly supported test functions, so the tempered distributions form a subspace of the space of all distributions on $G$. For $G=\mathbb R^m$ this is the classical density of $C_c^\infty(\mathbb R^m)$ in $\mathcal S(\mathbb R^m)$, and for $G=\mathbb Z^r$ the density of the finitely supported sequences among the rapidly decreasing ones. In the source this is how the space of tempered distributions on $G$ is viewed as a subspace of the space of all distributions on $G$.
--
--   **Formalization Note.** The statement is `Dense {f : SchwartzBruhat G | HasCompactSupport (f : G → ℂ)}` for the platform type `SchwartzBruhat G` with its inductive limit topology. An element of $\mathcal S(G)$ with compact support induces a compactly supported function on $\Gamma/k$ and conversely (the subgroup $k$ is compact), so this set is exactly $\mathcal D(G)$. No countability assumption is made.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 777, §D.1.8 (second paragraph); classical reference: A. A. Kirillov and A. D. Gvishiani, Theorems and Problems in Functional Analysis, Springer-Verlag, 1982, Theorem 30, p. 74 (the case of $\mathbb R^m$, as cited in the source)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_hasCompactSupport_dense
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] :
    Dense {f : SchwartzBruhat G | HasCompactSupport (f : G → ℂ)} := by sorry

end MasulloGRH
