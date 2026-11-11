-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_lemma_2_13
-- name    : HDXNbhdPCP.Main.lemma_2_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:59:07.483693+00:00
-- url     : https://prove2.me/theorems/c4c63393-1224-402b-ba02-4a5afe11e5e5
-- title:
--   Lemma 2.13 — colour merging preserves $\varepsilon$-products
-- statement:
--   Let $K$ be a weighted $I$-coloured complex ($I$ finite) and $\varepsilon\in[0,1]$. If $K$ is an $\varepsilon$-product (every two-colour graph $K_\sigma[i,j]$ of every link, $\sigma=\emptyset$ included, is an $\varepsilon$-expander), then for every pair of distinct colours $a\ne b$ the colour-merged complex $K\langle a\sqcup b\rangle$ (colours $(I\setminus\{a,b\})\cup\{\star\}$, $K\langle a\sqcup b\rangle[\star]=K[a]\sqcup K[b]$, facet law that of $(x_R,x_c)$ with $c$ uniform in $\{a,b\}$) is an $\varepsilon$-product:
--   $$K\ \varepsilon\text{-product}\ \Longrightarrow\ K\langle a\sqcup b\rangle\ \varepsilon\text{-product}.$$
--
--   It is used to transfer the expansion of the KMS complex to the merged test of Theorem 6.1.
--
--   Differences from the source:
--   - encoding: weighted coloured complex with a full-support facet distribution; links K_σ → FinDist on the product of the vertex types with IsProb; the link of y_J is the facet distribution conditioned on x_J = y_J; reason: the facets are the support and the vertex sets the images of the support, so every vertex lies in a facet; same instances
--   - encoding: the new colour ⋆ and the uniform choice c ∈ {a, b} → the colour none of Option {i // i ≠ a ∧ i ≠ b} and a uniform coin in Bool; reason: same complex
--   - encoding: ε ∈ [0, 1] as part of Definition 2.11 → hypotheses 0 ≤ ε ≤ 1; reason: IsProduct carries no range; the hypotheses restore Definition 2.11's
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 15, Lemma 2.13

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex

namespace HDXNbhdPCP.Main

/-- Lemma 2.13: merging two distinct colours of an `ε`-product gives an `ε`-product. -/
theorem lemma_2_13 {I : Type} [Fintype I] {V : I → Type} (K : ColoredComplex I V)
    (hK : FinDist.IsProb K) (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (hprod : K.IsProduct ε)
    (a b : I) (hab : a ≠ b) : (K.merge a b).IsProduct ε := by sorry

end HDXNbhdPCP.Main
