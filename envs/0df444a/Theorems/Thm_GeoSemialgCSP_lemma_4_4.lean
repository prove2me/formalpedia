-- Prove2me | Theorems.Thm_GeoSemialgCSP_lemma_4_4
-- name    : GeoSemialgCSP.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:47.261204+00:00
-- url     : https://prove2.me/theorems/57a41adb-4321-4c11-9ce9-41d6d244f5ca
-- title:
--   Lemma 4.4 — dictator completeness
-- statement:
--   Assume the standing hypotheses of Section 4: $k\ge2$; $P$ is the restriction to $X^k$ of a semialgebraic predicate $S$ on $(\mathbb R^d)^k$; $(X,P)$ has property (2); $h\ge1$ is a height with the property of Lemma 4.1 for $q_0\ge1$ and $\varepsilon>0$; and $L$ is a random map with items 1–3 of Lemma 4.2 for error $\varepsilon_L>0$. Let $0<\eta<1$ and $\varepsilon'>0$ with $\varepsilon_L+k\eta\le\varepsilon'$, and let $\psi_M:[M]\to X$ be a cousins homomorphism of $T_M$. Then
--
--   1. for every $R$ and every coordinate $r$, the dictator $\phi^{(r)}(z)=\psi_M(z_r)$ satisfies
--   $$\mathrm{val}(\phi^{(r)},(D_R)_P)\ \ge\ 1-\varepsilon' ;$$
--   2. in particular, for $R\ge1$ the test is $(1-\varepsilon')$-satisfiable: some assignment of points of $X$ to $[M]^R$ has value at least $1-\varepsilon'$.
--
--   This is the completeness of the dictatorship test.
--
--   Differences from the source:
--   - encoding: a predicate P : (ℝ^d)^k → {0,1}, semialgebraic in the k·d coordinates → its accepting set S ⊆ (EuclideanSpace ℝ (Fin d))^k, semialgebraic through finProdFinEquiv; reason: the same predicate; P(x) = 1 iff x ∈ S
--   - generalization: property (2): a cousins homomorphism for every finite ordered k-ary tree → HasCousinsHoms: one for every complete ordered k-ary tree; reason: a weaker hypothesis: every finite ordered k-ary tree embeds in a complete one preserving cousins tuples, so the printed property implies it; the proof uses only complete trees (Lemma 4.3 item 4)
--   - encoding: leaves of T_m and of T_M numbered 0, …, m−1 and 0, …, M−1 with M = k^H → words Fin h → Fin k and Fin H → Fin k; reason: a leaf's number is the base-k value of its word
--   - encoding: r ∈ {1, …, R} → r : Fin R; reason: index base
--   - generalization: R ≥ 1 (Let R ≥ 1, p.11) → every R : ℕ; reason: the R ≥ 1 cases are included; at R = 0 the test has a single variable and the inequality also holds
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.4, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_IsSemialgebraicPred
import Definitions.Def_GeoSemialgCSP_HasCousinsHoms
import Definitions.Def_GeoSemialgCSP_CousinsHom
import Definitions.Def_GeoSemialgCSP_MSSound
import Definitions.Def_GeoSemialgCSP_RE1
import Definitions.Def_GeoSemialgCSP_RE2
import Definitions.Def_GeoSemialgCSP_RE3
import Definitions.Def_GeoSemialgCSP_valDord

namespace GeoSemialgCSP

/-- **Lemma 4.4 (dictator completeness).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.4, printed p.12 (PDF p.13): with
`ε_L + kη ≤ ε'`, for every coordinate `r`, the dictator `ϕ^{(r)}(z) = ψ_M(z_r)` has
`val(ϕ^{(r)}, (D_R)_P) ≥ 1 − ε'`; in particular the test is `(1 − ε')`-satisfiable.

**Formalization Note.** The standing assumptions of §4 are hypotheses: `k ≥ 2`, `P` the restriction
to `X^k` of a semialgebraic predicate, property (2), a height `h ≥ 1` satisfying Lemma 4.1 for
`q₀, ε` (`h ≥ 1` is what makes the template have total weight one, p.9),
and `L` with items 1–3 of Lemma 4.2 at error `ε_L`; `ψ_M` is a cousins homomorphism of `T_M`
(Lemma 4.3 item 4). The second clause is "in particular, the test is `(1 − ε')`-satisfiable"
(an assignment into `X` of value at least `1 − ε'`), for `R ≥ 1`. -/
theorem lemma_4_4 {k d : ℕ} (hk : 2 ≤ k) (X : Set (E d)) (S : Set (Fin k → E d))
    (hsa : IsSemialgebraicPred S) (hcous : HasCousinsHoms X S)
    (q₀ : ℕ) (ε : ℝ) (hq₀ : 1 ≤ q₀) (hε : 0 < ε) {h H : ℕ} (hh : 1 ≤ h) (hms : MSSound k q₀ ε h)
    (L : PMF ((Fin h → Fin k) → Wd k H)) (εL : ℝ) (hεL : 0 < εL)
    (hL1 : RE1 L) (hL2 : RE2 L) (hL3 : RE3 L εL)
    (η ε' : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hε' : 0 < ε') (hsum : εL + k * η ≤ ε')
    (ψ : Wd k H → E d) (hψ : CousinsHom X S H ψ) (R : ℕ) :
    (∀ r : Fin R, 1 - ε' ≤ valDord L R η S (fun z => ψ (z r))) ∧
      (0 < R → ∃ ϕ : (Fin R → Wd k H) → E d, (∀ z, ϕ z ∈ X) ∧ 1 - ε' ≤ valDord L R η S ϕ) := by sorry

end GeoSemialgCSP
