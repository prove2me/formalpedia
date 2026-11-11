-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_lemma_3_10
-- name    : HDXNbhdPCP.Main.lemma_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:59:44.772439+00:00
-- url     : https://prove2.me/theorems/fbea96f6-89a6-4825-8565-bb70eb4f86ef
-- title:
--   Lemma 3.10 — from processed lists to vertex candidates
-- statement:
--   Let $Z$ be a weighted 6-partite complex with $Y=Z[4,5,6]$ and, for a vertex $y$ of $Y$, let $X_y[2]$ be the colour-2 vertices of its link. Let $m\ge1$, $\varepsilon>0$, $\beta>0$, $\eta\in\mathbb R$, and let $\Sigma$ be a finite alphabet. Suppose that
--
--   1. every vertex $y\in Y(0)$ carries a list $L'_y=(g_{y,1},\dots,g_{y,m})$ of functions on $X_y[2]$, and every oriented edge $(y,y')\in Y(1)$ a permutation $\pi_{(y,y')}$ of the positions, with $\pi_{(y',y)}=\pi_{(y,y')}^{-1}$;
--   2. (edge consistency) $\Pr_{(y,y')\sim Y(1)}\big[\forall i:\ \mathrm{dist}_{X_{(y,y')}[2]}(g_{y,i},g_{y',\pi_{(y,y')}(i)})\le\eta/10000\big]\ge1-K_{\rm in}\varepsilon^{12}$;
--   3. (triangle consistency) $\Pr_{(y,y',y'')\sim Y(2)}\big[\pi_{(y'',y)}\circ\pi_{(y',y'')}\circ\pi_{(y,y')}=\mathrm{Id}\big]\ge1-K_{\rm in}\varepsilon^{12}$;
--   4. $h^1(Y,\mathrm{Sym}(m))\ge\beta$, and $h^1(Y,\mathrm{Sym}(2))\ge\beta$ (the case $m=2$ of the standing hypothesis 2 of Theorem 3.2).
--
--   Then there is an ensemble $\mathcal G=\{g_y\}_{y\in Y(0)}$ with $g_y\in L'_y$ such that
--   $$\Pr_{(y,y')\sim Y(1)}\Big[\mathrm{dist}_{X_{(y,y')}[2]}(g_y,g_{y'})\le\frac{\eta}{10000}\Big]\ge1-K_{\rm out}\,\frac{\varepsilon^{12}}{\beta},$$
--   where for every constant $K_{\rm in}$ of the hypotheses there is a constant $K_{\rm out}$ that works for all such data.
--
--   This is the step where coboundary expansion over symmetric groups turns triangle-consistent lists into a single candidate per vertex.
--
--   Differences from the source:
--   - generalization: the §3 context: Z satisfying Theorem 3.2's hypotheses, F with Agr(F) = ε, ε below a small constant, L′_y ⊂ L⁰_y from Lemma 3.4 → any weighted 6-partite Z, any lists of m functions, any ε > 0 and η; of the context only h¹(Y, Sym(2)) ≥ β (hypothesis 2 of Theorem 3.2 at m = 2 ≤ ε₀^{-C}) is kept; reason: the proof uses only the coboundary bound and the edge and triangle guarantees; h¹(Y, Sym(2)) ≥ β bounds β by 3, which the O(ε¹²/β) form needs (with Sym(1) alone β is unbounded); the §3 objects satisfy every hypothesis
--   - reading: 'satisfy the guarantees of Theorem 3.5', with O(ε¹²), and the conclusion O(ε¹²/β) → probabilities ≥ 1 − K_in ε¹²; for every K_in there is K_out with conclusion ≥ 1 − K_out ε¹²/β; reason: the conclusion's constant depends on Theorem 3.5's constant only
--   - reading: triangle consistency printed as π_(y,y′) ∘ π_(y′,y″) ∘ π_(y″,y) = Id (Theorem 3.5) → π_(y″,y) ∘ π_(y′,y″) ∘ π_(y,y′) = Id; reason: typo: the printed composition is undefined for maps L_y → L_y′; Lemma 3.9 and the proof of Lemma 3.10 use this loop (INSIGHTS I4)
--   - encoding: sub-lists L′_y and permutations π_(y,y′) : L′_y → L′_y′ → families i ↦ Lst y i over Fin m and permutations of Fin m; π_(y′,y) = π_(y,y′)⁻¹ (footnote 6) as a hypothesis; reason: a list is its positions; the footnote is the paper's convention
--   - encoding: colours 1, …, 6; Y(1), Y(2) with induced distributions → Fin 6 with 0-based colours, Y = colours 3, 4, 5; ordered edges and triangles from uniform ordered colour tuples; reason: the events are orientation-independent; same distributions on unordered faces
--   - encoding: a nonempty finite alphabet Σ → a type Sig : Type with Fintype (and Nonempty where the source asks for it); reason: every finite alphabet is in bijection with a type in Type 0
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 21, Lemma 3.10 (hypotheses: Theorem 3.5, p. 20, and footnote 6; standing assumptions of §3.1, p. 19)

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex
import Definitions.Def_HDXNbhdPCP_Main_Agreement

namespace HDXNbhdPCP.Main

/-- Lemma 3.10 (from processed lists to vertex candidates). `Z` is 6-partite (colours `0, …, 5`),
`Y = Z[3, 4, 5]`; the list at a vertex `y` of `Y` is `i ↦ Lst y i` (`i ∈ [m]`), a list of functions
on `X_y[2]` (colour-`1` vertices); `π y y'` permutes list positions along the oriented edge
`(y, y')`. The `O(ε¹²)` of Theorem 3.5's guarantees is `K_in ε¹²`; the conclusion's
`O(ε¹²/β)` is `K_out ε¹²/β`. The coboundary bound over `Sym(2)` is the part of §3's standing
hypotheses (Theorem 3.2, hypothesis 2) that the bound `O(ε¹²/β)` relies on. -/
theorem lemma_3_10 :
    ∀ K_in : ℝ, ∃ K_out : ℝ,
    ∀ (V : Fin 6 → Type) (Z : ColoredComplex (Fin 6) V), FinDist.IsProb Z →
    ∀ (Sig : Type) [Fintype Sig] (ε η β : ℝ), 0 < ε → 0 < β →
    ∀ (m : ℕ), 0 < m →
    ∀ (Lst : ColoredComplex.CVert V → Fin m → (V 1 → Sig))
      (π : ColoredComplex.CVert V → ColoredComplex.CVert V → Equiv.Perm (Fin m)),
      -- `π_{(y', y)} = π_{(y, y')}⁻¹` (footnote 6)
      (∀ p ∈ (Z.edgeDistOn {3, 4, 5}).supp, π p.2 p.1 = (π p.1 p.2)⁻¹) →
      -- edge consistency
      (Z.edgeDistOn {3, 4, 5}).prob (fun p => ∀ i : Fin m,
          AgreementTest.distOn
            (FinDist.map (FinDist.cond Z (fun x => x p.1.1 = p.1.2 ∧ x p.2.1 = p.2.2))
              (fun x => x 1))
            (Lst p.1 i) (Lst p.2 (π p.1 p.2 i)) ≤ η / 10000) ≥ 1 - K_in * ε ^ 12 →
      -- triangle consistency (`y → y' → y'' → y` is the identity)
      (Z.triDistOn {3, 4, 5}).prob (fun t =>
          π t.2.2 t.1 * π t.2.1 t.2.2 * π t.1 t.2.1 = 1) ≥ 1 - K_in * ε ^ 12 →
      Z.HasCobExpOn {3, 4, 5} (Equiv.Perm (Fin m)) β →
      -- §3 standing assumption (Theorem 3.2, hypothesis 2, at `m = 2 ≤ ε₀^{-C}`)
      Z.HasCobExpOn {3, 4, 5} (Equiv.Perm (Fin 2)) β →
      ∃ G : ColoredComplex.CVert V → (V 1 → Sig), (∀ y, ∃ i, G y = Lst y i) ∧
        (Z.edgeDistOn {3, 4, 5}).prob (fun p =>
          AgreementTest.distOn
            (FinDist.map (FinDist.cond Z (fun x => x p.1.1 = p.1.2 ∧ x p.2.1 = p.2.2))
              (fun x => x 1))
            (G p.1) (G p.2) ≤ η / 10000) ≥ 1 - K_out * ε ^ 12 / β := by sorry

end HDXNbhdPCP.Main
