-- Prove2me | Theorems.Thm_OAI_TreeEdit_binary_transfer
-- name    : OAI.TreeEdit.binary_transfer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:19:18.141323+00:00
-- url     : https://prove2.me/theorems/db3b397b-d12b-401f-aa19-96674e1411e8
-- title:
--   Separation plus Lipschitz averaging yields an $\ell_1$-distortion lower bound for binary strings
-- statement:
--   For finite words $u,v$ over an alphabet, $\operatorname{ed}(u,v)$ is the edit distance: the least number of single-symbol insertions, deletions or substitutions (at any position, with no restriction on intermediate lengths) turning $u$ into $v$. Let $\ell_1=\ell_1(\mathbb N)$ be the real Banach space of absolutely summable sequences with metric $\|F-G\|_1$. For a finite set $W$ of binary strings and a map $f:W\to\ell_1$ the distortion is
--   $$
--   \operatorname{dist}(f)=\max_{u\ne v}\frac{\|f(u)-f(v)\|_1}{\operatorname{ed}(u,v)}\cdot\max_{u\ne v}\frac{\operatorname{ed}(u,v)}{\|f(u)-f(v)\|_1}
--   $$
--   (maxima over distinct $u,v\in W$), and $c_1(W)=\inf\{\operatorname{dist}(f): f:W\to\ell_1\ \text{injective}\}$ is the least $\ell_1$-distortion of $W$ under edit distance. For a binary block code $c:\Gamma\to\{0,1\}^P$ and a word $u=u_1\cdots u_n$ over $\Gamma$ let $E(u)=c(u_1)\cdots c(u_n)$ be its concatenation encoding.
--
--   **Theorem.** Let $A$ be a finite abelian group, $\Gamma$ a finite alphabet, $M,P\ge 1$ integers, $w:A\to\Gamma^M$ a map assigning to each group element a word of length $M$, $z\in A$, $c:\Gamma\to\{0,1\}^P$ a binary block code, and $a,b>0$ real numbers. Assume:
--
--   1. (code) $\dfrac{P}{804}\,\operatorname{ed}(u,v)\le\operatorname{ed}(E(u),E(v))$ for all $u,v\in\Gamma^M$;
--   2. (separation) $M\le a\cdot\operatorname{ed}\big(w(x),w(x+z)\big)$ for all $x\in A$;
--   3. (averaging) for every map $F:A\to\ell_1$ and every real $C\ge 0$ such that $\|F(x)-F(y)\|_1\le C\,\operatorname{ed}(w(x),w(y))$ for all $x,y\in A$, one has $\frac{1}{|A|}\sum_{x\in A}\|F(x)-F(x+z)\|_1\le C\,M\,b$.
--
--   Then there is a finite set $W$ of binary strings with $|W|\ge 2$, all of length $MP$, such that
--   $$
--   c_1(W)\ge\frac{1}{804\,a\,b}.
--   $$
--
--   This is an abstract transfer principle: a group-indexed family of words that moves far under the shift $z$, while every edit-Lipschitz map into $\ell_1$ moves little on average under $z$, produces a set of binary strings (namely the encodings $E(w(x))$) whose edit metric embeds into $\ell_1$ only with large distortion. In the main argument it is applied with the trivial code on $\{0,1\}$ ($P=1$).
--
--   **Formalization Note** The two maxima are `sSup` of finite sets of ratios (`distortion`), $c_1$ is the `sInf` in `c1`, the average is `FiniteFourier.average`, and $\ell_1$ is `lp (fun _ : ℕ => ℝ) 1`. The code hypothesis quantifies over all pairs of words of length $M$, not only over words in the image of $w$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/DistortionTransfer.lean#L68-L138

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters
import Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter
import Definitions.Def_OAI_Combinatorics_TreeEdit_DistortionTransfer

open OAI OAI.TreeEdit
universe u
attribute [local instance] Classical.propDecidable

theorem OAI.TreeEdit.binary_transfer {A Γ : Type*} [Fintype A] [AddCommGroup A] [Fintype Γ]
    {M P : ℕ} (hM : 0 < M) (hP : 0 < P) (w : A → Word Γ M) (z : A)
    (c : Γ → Word Bool P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hcode : ∀ x y : Word Γ M,
      (P : ℝ) / 804 * ed x.val y.val ≤ ed (encode c x.val) (encode c y.val))
    (hsep : ∀ x, (M : ℝ) ≤ a * ed (w x).val (w (x + z)).val)
    (hobs : ∀ (F : A → RealL1) (C : ℝ), 0 ≤ C →
      (∀ x y, dist (F x) (F y) ≤ C * ed (w x).val (w y).val) →
      FiniteFourier.average (fun x => dist (F x) (F (x + z))) ≤ C * M * b) :
    ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ v ∈ W, v.length = M * P) ∧
      (804 * a * b)⁻¹ ≤ c1 W := by sorry
