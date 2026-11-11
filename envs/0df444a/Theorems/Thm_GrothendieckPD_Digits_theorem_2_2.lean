-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_theorem_2_2
-- name    : GrothendieckPD.Digits.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:19.938318+00:00
-- url     : https://prove2.me/theorems/3f6f2d6d-e07e-4300-b4a4-3e5869d9e699
-- title:
--   Theorem 2.2: duality $1/K_G=\sup_{c\in\mathcal C}(c_1-\sum|c_m|)=\inf_{q\in\mathcal Q}v_\infty(q)$, infimum attained
-- statement:
--   Let $\mathcal C\subseteq\ell_1$ be the set of sequences $c(\mu)$, where $n\in\mathbb N$ and $\mu$ ranges over distributions on pairs of odd functions $f,g:\mathbb R^n\to\{\pm1\}$, and let $\mathcal Q=\{q\in\ell_\infty:q_1=1,\ |q_m|\le1\ \forall m,\ q_{2m}=0\}$. Then:
--
--   1. for every $q\in\mathcal Q$, $v_\infty(q)=\sup_{c\in\mathcal C}\langle c,q\rangle$;
--   2. $$\frac1{K_G}=\sup\Bigl\{c_1-\sum_{\text{odd }m\ge3}|c_m|:c\in\mathcal C\Bigr\}=\inf\{v_\infty(q):q\in\mathcal Q\};$$
--   3. the infimum over $q$ is attained.
--
--   The theorem identifies the two certificate types of the paper, Krivine rounding schemes (upper bounds) and Hermite projection games (lower bounds), as primal and dual of one convex program for $1/K_G$.
--
--   Differences from the source:
--   - reading: odd functions f, g : ℝⁿ → {±1} → f(−x) = −f(x) for γₙ-almost every x; reason: pointwise oddness is impossible for ±1-valued functions (f(0) = −f(0)); a.e. oddness is the only satisfiable meaning and every Hermite coefficient depends only on the a.e. class
--   - encoding: f, g : ℝⁿ → {±1} → measurable functions with values in {1, −1} (GrothendieckLB.IsSignFn); reason: Hermite coefficients require measurability; the source states it in Lemma 2.5 and uses it throughout
--   - reading: a distribution µ on pairs of functions → a jointly measurable random pair (F, G) over a probability space (Ω, µ) (GrothendieckLB.MixedScheme); reason: the source fixes no σ-algebra on a space of functions; the random-pair reading contains every finite mixture and makes ω ↦ c_m(F ω, G ω) measurable
--   - encoding: c_m(f, g) = ⟨Π_m f, Π_m g⟩ → the moment sum ∑_{|α| = m} E[f He_α] E[g He_α] / α! (GrothendieckLB.pmInner); reason: same value by orthonormality of ψ_α = He_α/√α!
--   - reading: v_∞(q) = sup_{c∈𝒞} ⟨c, q⟩ → asserted for every q ∈ 𝒬; reason: the proof derives it from Lemma 2.6, which needs q ∈ 𝒬
--   - reading: q_{2m} = 0 for m ∈ ℕ → also q_0 = 0; reason: ℕ ∋ 0 here: Lemma 2.6 writes Q = ∑_{odd m} q_m Π_m, and with q_0 ≠ 0 the identity v_∞(q) = sup_𝒞⟨c,q⟩ fails (constant f = g = 1)
--   - encoding: ℓ1, ℓ∞ and ⟨c, q⟩ → sequences ℕ → ℝ, |q_m| ≤ 1, ⟨c, q⟩ = ∑' c_m q_m; reason: 𝒞 ⊆ ℓ1 by Lemma 2.5 and |q_m| ≤ 1 gives q ∈ ℓ∞
--   - encoding: sup and inf in (2.2) → IsLUB and IsGLB at 1/K_G; reason: avoids Lean's sSup/sInf default; same statement
--   - encoding: K_G = sup_{m,n} sup_{A} SDP(A)/OPT(A) (Eq. 1.1) → K_G = inf{K : SDP(A) ≤ K·OPT(A) for all real matrices A} (published GrothendieckConstant.grothendieckConst), with unit vectors in ℝ^d for arbitrary d; reason: same value: the ratio is undefined only at A = 0, where both sides vanish; OPT(A) > 0 for A ≠ 0; the admissible set is nonempty (Grothendieck's inequality) and bounded below; unit vectors in any dimension give the same SDP value as in ℝ^{m+n}
--   - encoding: the sum over odd degrees m ≥ 3 → the sum over k : ℕ with m = 2*k + 3; reason: a bijective reindexing of every odd degree at least 3
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Theorem 2.2, p. 4, Eq. (2.2)

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames

namespace GrothendieckPD.Digits

/-- Theorem 2.2 (p. 4), all clauses: for every `q ∈ 𝒬`, `v_∞(q) = sup_{c ∈ 𝒞} ⟨c, q⟩`;
`1/K_G = sup{c_1 - ∑_{odd m ≥ 3} |c_m| : c ∈ 𝒞} = inf{v_∞(q) : q ∈ 𝒬}` (Eq. 2.2), each as a
least upper / greatest lower bound; and the infimum over `q` is attained. -/
theorem theorem_2_2 :
    (∀ q ∈ QSet, IsLUB {s : ℝ | ∃ c ∈ CSet, s = pairing c q} (gameValueInf q)) ∧
    IsLUB {s : ℝ | ∃ c ∈ CSet, s = krivineValue c}
      (GrothendieckConstant.grothendieckConst)⁻¹ ∧
    IsGLB {s : ℝ | ∃ q ∈ QSet, s = gameValueInf q}
      (GrothendieckConstant.grothendieckConst)⁻¹ ∧
    ∃ q ∈ QSet, gameValueInf q = (GrothendieckConstant.grothendieckConst)⁻¹ := by sorry

end GrothendieckPD.Digits
