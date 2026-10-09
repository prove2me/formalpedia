-- Prove2me | Theorems.Thm_OAI_Erdos3_LocalConvolution_exists_sifted_almostPeriods
-- name    : OAI.Erdos3.LocalConvolution.exists_sifted_almostPeriods
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:43:57.67501+00:00
-- url     : https://prove2.me/theorems/b322c79c-89c5-45ac-aa3c-bb33e66bbbfa
-- title:
--   A large correlation moment yields dense sets with a Bohr set of almost periods
-- statement:
--   Let $N$ be a positive natural number (`[NeZero N]`). A `CyclicBohr.Set N` is OpenAI's structure bundling a finite set of frequencies in $\mathbb{Z}/N$ and a radius $\rho \ge 0$; its `carrier` is the finite set of $x$ with $\|1 - \chi_r(x)\| \le \rho$ for every frequency $r$ ($\chi_r$ the additive character `CyclicBohr.character r`), its `rank` is the number of frequencies, `ndilate t` scales the radius by $t \in \mathbb{R}_{\ge 0}$, and `IsRankRegular` is OpenAI's regularity predicate on carrier sizes of the dilates by $1 \pm \kappa$; below a Bohr set stands for its carrier where a set is meant.
--
--   Let $L, S, B_0$ be Bohr sets with $L$ rank-regular, $0 < \rho_{B_0} \le 1$, $B_0$ rank-regular and $1 \le \operatorname{rank} B_0$. Let $T, K$ be finite subsets of $\mathbb{Z}/N$ with $T$ nonempty, and $z \in \mathbb{Z}/N$, with $|T| = |B_0|$ and $b - z \in B_0$ for all $b \in T$. Let $\kappa \in \mathbb{R}_{\ge 0}$ with $S \subseteq$ `L.ndilate κ` and $\kappa \le 1/(100 \cdot 2\max(\operatorname{rank} L, 1))$. Let $f : \mathbb{Z}/N \to \mathbb{R}$ vanish off $L$. Let $M, \alpha, \theta, \varepsilon, \eta, p, C$ be reals with $0 < M$, $1 \le \alpha$, $0 \le \theta$, $0 < \varepsilon$, $0 < \eta \le 1$, $1 \le p$, $0 \le C$, $M \le e^{p}$, and $0 \le f(x) \le M$ for all $x$. Let $q \in \mathbb{N}$ with $q \le C p$, and suppose
--   $$\alpha^q \le \mathbb{E}_{a \in S}\, \mathbb{E}_{b \in T}\, \phi(a - b)^q, \qquad \phi = \texttt{correlation}\ L\ f\ f,\quad \phi(t) = \tfrac{1}{|L|}\textstyle\sum_x f(x+t) f(x),$$
--   that $\phi(a - b) \le \theta$ whenever $a \in S$, $b \in T$ and $a - b \notin K$, that $\theta^q \le \tfrac{\varepsilon}{2} \alpha^q$, and that $|K| \le 2|S|$. Put $D = (3C + 1) p^2$. Then there exist $A \subseteq S$ and $B \subseteq T$, both nonempty, with $e^{-D} |S| \le |A|$ and $e^{-D} |B_0| \le |B|$, and a Bohr set $R$ such that $R$ is rank-regular, $0 < \rho_R \le 1$, $R \subseteq B_0$,
--   $$\operatorname{rank} R \le \operatorname{rank} B_0 + c_\eta (1 + D)^4, \qquad \rho_{B_0} \exp\bigl(-c_\eta (1 + D + \log(2 + \operatorname{rank} B_0))\bigr) \le \rho_R,$$
--   where $c_\eta = $ `almostPeriodicityWidthConstant η` (an explicit real constant depending on $\eta$), and
--   $$1 - \varepsilon - \eta \le \texttt{smoothedDifferenceEventProbability}\ A\ B\ K\ R,$$
--   the latter being $\mathbb{E}_{t \in R}\, \mathbb{E}_{a \in A}\, \mathbb{E}_{b \in B}\, \mathbf{1}_K(a - b + t)$.
--
--   Lean: `OAI.Erdos3.LocalConvolution.exists_sifted_almostPeriods` in `lean/OAI/Combinatorics/Progressions/Estimates/LocalizedSiftingAlmostPeriods.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/LocalizedSiftingAlmostPeriods.lean#L463

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open RelativeChangSanders
open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicCrootSisask

open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise NNReal

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

theorem exists_sifted_almostPeriods
    (L S B₀ : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hBpos : 0 < B₀.radius) (hBwidth : B₀.radius ≤ 1)
    (hBreg : B₀.IsRankRegular) (hBrank : 1 ≤ B₀.rank)
    (T K : Finset (ZMod N)) (hT : T.Nonempty) (z : ZMod N)
    (hTcard : T.card = B₀.carrier.card) (hTB : ∀ b ∈ T, b - z ∈ B₀.carrier)
    {kappa : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M alpha threshold epsilon eta p C : ℝ}
    (hM : 0 < M) (halpha : 1 ≤ alpha) (hthreshold : 0 ≤ threshold)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hcap : M ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (q : ℕ) (hq : (q : ℝ) ≤ C * p)
    (hmoment : alpha ^ q ≤ 𝔼 a ∈ S.carrier, 𝔼 b ∈ T, correlation L.carrier f f (a - b) ^ q)
    (hbad : ∀ a ∈ S.carrier, ∀ b ∈ T, a - b ∉ K → correlation L.carrier f f (a - b) ≤ threshold)
    (hseparation : threshold ^ q ≤ epsilon / 2 * alpha ^ q)
    (hK : K.card ≤ 2 * S.carrier.card) :
    let D := (3 * C + 1) * p ^ 2
    ∃ A ⊆ S.carrier, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      Real.exp (-D) * S.carrier.card ≤ A.card ∧
      Real.exp (-D) * B₀.carrier.card ≤ B.card ∧
      ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
        R.carrier ⊆ B₀.carrier ∧
        (R.rank : ℝ) ≤ B₀.rank + almostPeriodicityWidthConstant eta * (1 + D) ^ 4 ∧
        B₀.radius * Real.exp (-(almostPeriodicityWidthConstant eta *
          (1 + D + Real.log (2 + B₀.rank)))) ≤ R.radius ∧
        1 - epsilon - eta ≤ smoothedDifferenceEventProbability A B K R.carrier := by
  sorry

end Erdos3.LocalConvolution
end
end OAI
