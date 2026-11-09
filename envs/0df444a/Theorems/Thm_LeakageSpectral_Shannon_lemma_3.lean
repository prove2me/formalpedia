-- Prove2me | Theorems.Thm_LeakageSpectral_Shannon_lemma_3
-- name    : LeakageSpectral.Shannon.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:14.187423+00:00
-- url     : https://prove2.me/theorems/4789d608-c5c3-41be-99e6-6b0b48872ee4
-- title:
--   Lemma 3, p. 26 — second-order approximation of $D_{\mathrm{KL}}$ by $\chi^2$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for all discrete probability distributions $p,q$ on a set $\mathcal X$ with $\operatorname{supp}(p)\subseteq\operatorname{supp}(q)$. Put $r(x)=p(x)/q(x)-1$ for $x\in\operatorname{supp}(q)$, and let $R<1$ be any bound on $|r|$, in particular $R=\|r\|_\infty$ when $\|r\|_\infty<1$. Then
--
--   $$
--   \Big|D_{\mathrm{KL}}(p\|q)-\frac{\chi^2(p\|q)}{2\ln2}\Big|\le C\,R^3,
--   $$
--
--   and there is a real $E$ with $|E|\le C\,R$ such that
--
--   $$
--   D_{\mathrm{KL}}(p\|q)=\frac{\chi^2(p\|q)}{2\ln2}\,(1+E).
--   $$
--
--   These are the additive and the relative forms of the approximation, in the source's convergence radius $\|r\|_\infty<1$.
--
--   Differences from the source:
--   - generalization: $O(\|r\|_\infty^3)$ and $1+O(\|r\|_\infty)$ "as $p\to q$" → one absolute constant $C$, chosen before $\mathcal X,p,q$, valid for every pair with a bound $R<1$ on $|r|$; reason: $(1+x)\ln(1+x)-x-x^2/2$ is at most a constant times $|x|^3$ on $[-1,1]$; this uniform bound implies the printed asymptotics, by taking $R=\|r\|_\infty\to0$, and covers the stated radius
--   - encoding: $r(x)=p(x)/q(x)-1$ "for any $x$" → $|r|$ is bounded only on $\operatorname{supp}(q)$; reason: off the support of $q$ the ratio is $0/0$; those points carry no mass since $\operatorname{supp}(p)\subseteq\operatorname{supp}(q)$
--   - encoding: $O(\cdot)$ in the relative form → an explicit real $E$ with $|E|\le C\,R$; reason: the meaning of the $O$; it avoids dividing by $\chi^2(p\|q)$, which vanishes at $p=q$
--   - encoding: discrete distributions on $\mathcal X$ → `PMF X` on any type `X`, with real masses `(p x).toReal`; reason: a PMF is a discrete distribution, with countable support
--   - reading: the printed support inclusion uses $\subset$ → `p.support ⊆ q.support`, allowing equality; reason: inclusion is read non-strictly, since proper inclusion would force $r=-1$ somewhere on the support of $q$, contradicting the stated radius $\|r\|_\infty<1$
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Appendix A, Lemma 3, p. 26; proof pp. 26–27

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
universe u

namespace LeakageSpectral.Shannon

/-- Lemma 3, p. 26: `D_KL(p ∥ q) = χ²(p ∥ q) / (2 ln 2) + O(‖r‖³_∞)` and
`D_KL(p ∥ q) = χ²(p ∥ q) / (2 ln 2) · (1 + O(‖r‖_∞))`, where `r(x) = p(x)/q(x) - 1` on the support of `q`,
with one absolute constant for all pairs of discrete distributions in the radius `‖r‖_∞ < 1`. `R` is
any bound on `|r|` below `1`, in particular `‖r‖_∞`. -/
theorem lemma_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type u} (p q : PMF X), p.support ⊆ q.support →
      ∀ R : ℝ, R < 1 → (∀ x ∈ q.support, |(p x).toReal / (q x).toReal - 1| ≤ R) →
        |discreteKLBits (fun x => (p x).toReal) (fun x => (q x).toReal) -
            chiSquareDiv (fun x => (p x).toReal) (fun x => (q x).toReal) / (2 * Real.log 2)| ≤ C * R ^ 3 ∧
        ∃ E : ℝ, |E| ≤ C * R ∧
          discreteKLBits (fun x => (p x).toReal) (fun x => (q x).toReal) =
            chiSquareDiv (fun x => (p x).toReal) (fun x => (q x).toReal) / (2 * Real.log 2) * (1 + E) := by sorry

end LeakageSpectral.Shannon
