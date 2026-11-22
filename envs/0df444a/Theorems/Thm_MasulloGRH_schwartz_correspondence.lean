-- Prove2me | Theorems.Thm_MasulloGRH_schwartz_correspondence
-- name    : MasulloGRH.schwartz_correspondence
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T16:14:17.961627+00:00
-- url     : https://prove2.me/theorems/c262db1e-b929-4df0-bebf-ac2c7b17c3b0
-- title:
--   Transport of Schwartz–Bruhat functions along a correspondence of elementary groups with compact kernels
-- statement:
--   Let $P$ be a Hausdorff locally compact abelian group, $P_0\le P$ an open subgroup, and let
--   $$E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times\textstyle\prod_{i<s}\mathbb Z/d_i,\qquad E'=\mathbb R^{m'}\times\mathbb T^{n'}\times\mathbb Z^{r'}\times\textstyle\prod_{i<s'}\mathbb Z/d'_i$$
--   be elementary abelian Lie groups, with $d_i\neq 0$. Let $\alpha\colon P_0\to E$ and $\beta\colon P\to E'$ be continuous, open homomorphisms with **compact kernels**. (Their images are open subgroups; they need not be surjective.)
--
--   For $g\in\mathcal S(E)$, let $f_g\colon P\to\mathbb C$ be $g\circ\alpha$ on $P_0$ and $0$ off $P_0$. Then there is a **continuous** linear map $T\colon\mathcal S(E)\to\mathcal S(E')$ such that for all $g$:
--   $$
--   (Tg)(\beta(p))=\int_{\ker\beta} f_g(pq)\,d\mu_{\ker\beta}(q)\quad(p\in P),\qquad (Tg)(e')=0\quad (e'\notin\beta(P)),
--   $$
--   where $\mu_{\ker\beta}$ is the normalized Haar measure of the compact group $\ker\beta$.
--
--   In words: Schwartz–Bruhat functions can be transported along the correspondence $E\xleftarrow{\alpha}P_0\subseteq P\xrightarrow{\beta}E'$. Pull back along $\alpha$, extend by zero, average over $\ker\beta$, and push down along $\beta$ (extending by zero off the open subgroup $\beta(P)$). The result is again Schwartz on $E'$, and it depends continuously on $g$.
--
--   This is the elementary-group core of Lemma D.1.5.4 and Theorem D.1.7.1 in Masullo's Appendix D. It combines averaging over a compact subgroup of an elementary group (Lemma D.1.6.18), pullback along continuous homomorphisms with compact kernel between elementary groups, and extension by zero from open subgroups. It implies `MasulloGRH.schwartzBruhatAverage_transfer`: take $P=\Gamma'$, $P_0=\Gamma\cap\Gamma'$, $\alpha=\pi|_{P_0}$ and $\beta=\pi'$.
--
--   **Formalization Note** $\mathcal S(E)$ is `ElemSchwartz` with the topology of the seminorms $\sup|a|^j|x|^i\|D^kg\|$ (Definition D.1.3.1). The averaged function is written as `schwartzBruhatAverage ⊤ β.ker f_g`, with `subgroupHaar` the normalized Haar measure, and $f_g$ is `extendPullback P₀ α g.toFun`. The hypothesis $d_i\neq0$ on the source is needed: for $d_i=0$ the factor $\mathbb Z/0=\mathbb Z$ carries no decay condition, and the statement would fail.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.1.5.4, Lemma D.1.6.18 and Theorem D.1.7.1 (pp. 762–770); F. Bruhat, Distributions sur un groupe localement compact, Bull. SMF 89 (1961)

import Definitions.Def_MasulloGRH_SchwartzBruhatAveraging

set_option autoImplicit false

namespace MasulloGRH

theorem schwartz_correspondence
    (P : Type*) [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    [LocallyCompactSpace P] (P₀ : Subgroup P) (hP₀ : IsOpen (P₀ : Set P))
    (m n r s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, d i ≠ 0)
    (α : ↥P₀ →* Multiplicative (ElemGroup m n r s d)) (hαc : Continuous α) (hαo : IsOpenMap α)
    (hαk : IsCompact {x : ↥P₀ | α x = 1})
    (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (β : P →* Multiplicative (ElemGroup m' n' r' s' d')) (hβc : Continuous β)
    (hβo : IsOpenMap β) (hβk : IsCompact {x : P | β x = 1}) :
    ∃ T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d', Continuous T ∧
      ∀ g : ElemSchwartz m n r s d,
        (∀ p : P, (T g).toFun (Multiplicative.toAdd (β p)) =
          schwartzBruhatAverage ⊤ β.ker (extendPullback P₀ α g.toFun) p) ∧
        ∀ e : ElemGroup m' n' r' s' d',
          e ∉ Set.range (fun p : P => Multiplicative.toAdd (β p)) → (T g).toFun e = 0 := by
  sorry

end MasulloGRH
