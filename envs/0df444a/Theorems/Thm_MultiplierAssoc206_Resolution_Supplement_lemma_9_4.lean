-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_Supplement_lemma_9_4
-- name    : MultiplierAssoc206.Resolution.Supplement.lemma_9_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:35:12.895595+00:00
-- url     : https://prove2.me/theorems/9e2acf10-2c21-4796-852a-0ecb54d80e10
-- title:
--   Lemma 9.4 — Reduction from PM(H) in bounded-depth Frege
-- statement:
--   Fix a Frege system and a strip-local multiplier encoding $\mathrm{Mul}_n$, and let $\Delta$ be a degree bound. There are constants $d_0$ and $s_0$, depending only on the Frege system, the encoding and $\Delta$, with the following property.
--
--   Let $H=(U,V,E)$ be a bipartite graph with $|U|=m+1$, $|V|=m$, maximum degree at most $\Delta$ and no isolated vertices; let index maps for $H$ with strip width $g=\lceil\log_2(m+2)\rceil+2$ and bound $n_0$ be given (the three properties of Lemma 7.3); and let $n\ge n_0$. Let $\mathrm{Assoc}_n$ be the associativity formula built from $\mathrm{Mul}_n$ and $\mathrm{PM}(H)$ the exact-one perfect-matching formula of $H$, both read as sets of Frege formulas. Then for every $d$, if $\pi$ is a Frege refutation of $\mathrm{Assoc}_n$ of depth at most $d$, there is a Frege refutation $\pi'$ of $\mathrm{PM}(H)$ with
--   $$\operatorname{depth}(\pi')\le d+d_0,\qquad|\pi'|\le s_0\,|\pi|.$$
--   Here $|\pi|$ is the total size of the formulas of $\pi$.
--
--   This transfers lower bounds for bounded-depth Frege refutations of perfect-matching formulas to $\mathrm{Assoc}_n$; with $H$ an odd grid and Håstad's lower bound for $\mathrm{PM}$ of the odd grid it yields Theorem 9.5.
--
--   **Formalization Note** The standing assumptions of Sections 5 and 8 ($H$, its degree bound, the index maps and $n\ge n_0$) are explicit binders, in the same order as in the published resolution analogue (Lemma 8.7): $d_0,s_0$ are chosen after the system, the encoding and $\Delta$, and before $m$, $H$, $n_0$, the index maps, $n$, $d$ and $\pi$. The objects $\mathrm{StripLocal}$, $\mathrm{Assoc}$, $\mathrm{PM}$ and the index maps are the published definitions of the base mission.
--
--   Differences from the source:
--   - reading: "there are constants d0 and s0" under the standing assumptions "as in Section 8" → d0 and s0 may depend on the Frege system, the encoding and the degree bound Δ, and are uniform over m, H, n0, the index maps, n, d and π; reason: the system is fixed throughout §9, the encoding by the standing assumption, and Δ by the standing assumptions of Section 5; this is the quantifier order of the published Lemma 8.7
--   - reading: the size of a formula is "its number of symbols" → symbols counted in prefix form; reason: the source does not fix a notation
--   - encoding: implicational completeness for every Γ → required only for finite Γ in the definition of a Frege system; reason: equivalent by the compactness theorem, so the same systems qualify
--   - encoding: a clause as a formula → the disjunction of its literals listed in one fixed order; reason: the source does not specify an order
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.24 (printed p.23), Lemma 9.4 (Reduction from PM(H)), with the standing assumptions of §9.3 (PDF p.24) and Section 5 (PDF pp.8–9)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Supplement_Frege
import Definitions.Def_MultiplierAssoc206_Resolution_Assoc
import Definitions.Def_MultiplierAssoc206_Resolution_IndexMaps

set_option autoImplicit false

namespace MultiplierAssoc206.Resolution.Supplement

/-- Lemma 9.4 (Reduction from PM(H)), PDF p.24 (printed p.23): for a Frege system and a
strip-local multiplier encoding there are constants `d₀`, `s₀` (depending only on the system,
the encoding and the degree bound `Δ`) such that, for every bipartite `H = (U, V, E)` with
`|U| = m + 1`, `|V| = m`, maximum degree at most `Δ` and no isolated vertices, every `n ≥ n₀`
for index maps of `H` with bound `n₀`, and every `d`, a depth-`d` Frege refutation `π` of
`Assoc_n` yields a depth-`(d + d₀)` Frege refutation of `PM(H)` of size at most `s₀ |π|`. -/
theorem lemma_9_4 (R : List Rule) (hR : IsFregeSystem R)
    (Mul : (n : ℕ) → MulEncoding n) (hMul : StripLocal Mul) (Δ : ℕ) :
    ∃ d₀ s₀ : ℕ, ∀ (m : ℕ) (U V : Type) [Fintype U] [Fintype V],
      Fintype.card U = m + 1 → Fintype.card V = m →
      ∀ E : Finset (U × V), MaxDegLE E Δ → NoIsolated E →
      ∀ (n₀ : ℕ) (_M : IndexMaps E (stripWidth m) n₀) (n : ℕ), n₀ ≤ n →
      ∀ (d : ℕ) (π : List (Formula (AVar Mul n))),
        IsRefutation R (cnfFormulas (Assoc Mul n)) π → derivDepth π ≤ d →
        ∃ π' : List (Formula (Edge E)), IsRefutation R (cnfFormulas (PM E)) π' ∧
          derivDepth π' ≤ d + d₀ ∧ derivSize π' ≤ s₀ * derivSize π := by sorry

end MultiplierAssoc206.Resolution.Supplement
