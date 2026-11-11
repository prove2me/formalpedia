-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_lemma_3_11
-- name    : HDXNbhdPCP.Main.lemma_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:59:57.766191+00:00
-- url     : https://prove2.me/theorems/e8fb9f6c-0d59-4896-aea6-1719a68f8fce
-- title:
--   Lemma 3.11 (= Lemma C.1) — the neighbourhood agreement test in the 99% regime
-- statement:
--   Let $H=(H[1],H[2],H[3])$ be a weighted 3-partite complex which is a $\lambda$-product, $0\le\lambda\le1$, let $\Sigma$ be a nonempty finite alphabet and $F=(f_u:H_u[2]\to\Sigma)_{u\in H[1]\cup H[3]}$ a local ensemble. For $\zeta>0$ let $\mathrm{Agr}_\zeta(F)$ be the probability, over $(u,v)\sim H[1,3]$, that $\mathrm{dist}_{H_{uv}[2]}(f_u,f_v)\le\zeta$. For every $\zeta,\alpha>0$,
--   $$\mathrm{Agr}_\zeta(F)>1-\alpha\ \Longrightarrow\ \exists g:H[2]\to\Sigma:\ \Pr_{y\sim H[1,3](0)}\Big[\mathrm{dist}_{H_y[2]}\big(f_y,g|_{H_y[2]}\big)\le1000(\zeta+\lambda)\Big]\ge1-1000(\alpha+\lambda),$$
--   where $y\sim H[1,3](0)$ picks a uniform colour in $\{1,3\}$ and then a vertex of that colour.
--
--   This is the high-soundness step of the local-to-global argument (§3.4), turning almost-everywhere consistent vertex candidates into one global function.
--
--   Differences from the source:
--   - reading: λ-local-spectral HDX (not defined in the paper) → λ-product (Definition 2.11) with 0 ≤ λ ≤ 1; reason: §2.5: 'every two-color graph in every link of Z is a λ-expander; equivalently, Z is a λ-product'; [0,1] is the range of Definition 2.11
--   - reading: g : X[2] → Σ, dist(g_y, g|X_y[2]) (printed) → g : H[2] → Σ and dist(f_y, g) on H_y[2]; reason: typo: the lemma is about H and its ensemble F = {f_y}; Lemma C.1 (p. 64) writes g : H[2] → Σ
--   - encoding: colours 1, 2, 3 of a 3-partite complex → Fin 3 with 0-based indices 0, 1, 2; reason: Lean convention; same instances
--   - encoding: local functions f_u : H_u[2] → Σ → functions V 1 → Sig read only on H_u[2]; reason: values outside H_u[2] never enter a distance
--   - encoding: a nonempty finite alphabet Σ → a type Sig : Type with Fintype (and Nonempty where the source asks for it); reason: every finite alphabet is in bijection with a type in Type 0
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 22, Lemma 3.11; restated with proof as Lemma C.1, p. 64

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex
import Definitions.Def_HDXNbhdPCP_Main_Agreement

namespace HDXNbhdPCP.Main

/-- Lemma 3.11 (= Lemma C.1): the neighbourhood agreement test in the 99% regime. The colours
`1, 2, 3` of the paper are `0, 1, 2`. -/
theorem lemma_3_11 {V : Fin 3 → Type} (H : ColoredComplex (Fin 3) V) (hH : FinDist.IsProb H)
    (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (hprod : H.IsProduct lam)
    {Sig : Type} [Fintype Sig] [Nonempty Sig] (F : V 0 ⊕ V 2 → V 1 → Sig) (ζ α : ℝ)
    (hζ : 0 < ζ) (hα : 0 < α) (hagr : H.approxAgr 0 1 2 F ζ > 1 - α) :
    ∃ g : V 1 → Sig,
      (H.outerVertexDist 0 2).prob (fun y =>
          AgreementTest.distOn ((H.nbhdTestOn 0 1 2).S y) (F y) g ≤ 1000 * (ζ + lam)) ≥
        1 - 1000 * (α + lam) := by sorry

end HDXNbhdPCP.Main
