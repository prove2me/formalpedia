-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_smaller_relation_instance
-- name    : OAI.TwoWayComplementation.smaller_relation_instance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:49:57.88262+00:00
-- url     : https://prove2.me/theorems/7ab61263-0a9d-4f62-a2b3-caac82ce2617
-- title:
--   Restricting to a retained label set inside an idempotent corner gives a smaller instance with unit lifts and a one-pair idempotent
-- statement:
--   For a set $H$ let $\mathcal B(H)$ be the monoid of binary relations on $H$, with product $RS=\{(x,z):\ (x,y)\in R\text{ and }(y,z)\in S\text{ for some }y\in H\}$ (composition in path order) and identity the equality relation $\mathrm{id}_H=\{(x,x):x\in H\}$. For a permutation $\sigma$ of $H$, its graph $G_\sigma=\{(x,\sigma(x)):x\in H\}$ is a unit of $\mathcal B(H)$ with inverse $G_{\sigma^{-1}}$. For $F\subseteq H$ let $\Delta_F=\{(x,x):x\in F\}$, and for $R\in\mathcal B(H)$ let $R|_F=\{(r,t)\in F\times F:(r,t)\in R\}$ be its restriction, an element of $\mathcal B(F)$. For an idempotent $d$ of a monoid $A$, the corner $dAd=\{w\in A:\ dw=w=wd\}$ is a monoid with identity element $d$.
--
--   Fix $m\in\mathbb N$ and let $[m]=\{0,\dots,m-1\}$. A *boundary diagram* is a quadruple $a=(a^{+},a^{-},a^{\mathrm L},a^{\mathrm R})$ of binary relations on $[m]$. They record traversals that enter on the left and exit on the right ($a^{+}$), enter on the right and exit on the left ($a^{-}$), or enter and exit on the left ($a^{\mathrm L}$) or on the right ($a^{\mathrm R}$). Relations are composed in path order, $(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$, and $R^{*}$ is the reflexive–transitive closure of $R$. The product
--   $$
--   ab=\Big(a^{+}(b^{\mathrm L}a^{\mathrm R})^{*}b^{+},\ \ b^{-}(a^{\mathrm R}b^{\mathrm L})^{*}a^{-},\ \ a^{\mathrm L}\cup a^{+}(b^{\mathrm L}a^{\mathrm R})^{*}b^{\mathrm L}a^{-},\ \ b^{\mathrm R}\cup b^{-}a^{\mathrm R}(b^{\mathrm L}a^{\mathrm R})^{*}b^{+}\Big)
--   $$
--   makes the set $\mathcal D_m$ of boundary diagrams a finite monoid with identity $(\mathrm{id},\mathrm{id},\varnothing,\varnothing)$. The corner of an idempotent $e$ is $\{z\in\mathcal D_m:\ ez=z=ze\}$.
--
--   For $e\in\mathcal D_m$ and a sign $s\in\{+,-\}$ put $K^{+}_e=(e^{\mathrm L}e^{\mathrm R})^{*}$, $K^{-}_e=(e^{\mathrm R}e^{\mathrm L})^{*}$ and $\mathrm{Rec}^{s}_e=K^{s}_e\,e^{s}\,K^{s}_e$. A *signed recurrent class* of $e$ is a pair $(s,C)$ such that, for some $x\in[m]$ with $(x,x)\in\mathrm{Rec}^{s}_e$, $C=\{y:\ (x,y)\in\mathrm{Rec}^{s}_e\text{ and }(y,x)\in\mathrm{Rec}^{s}_e\}$; let $\mathcal C(e)$ be the set of these classes. For $z\in\mathcal D_m$, the classes *missing* from $z$ relative to $e$ are
--   $$
--   \mathrm{Miss}_e(z)=\big\{(s,C)\in\mathcal C(e):\ (x,x)\notin K^{s}_e\,z^{s}\,K^{s}_e\ \text{ for every } x\in C\big\},
--   $$
--   the recurrent classes of $e$ none of whose loops survive when the through relation $e^{s}$ is replaced by $z^{s}$. For a finite set $X$, $|X|$ is its number of elements.
--
--   Let $A$ be a finite monoid, $H$ a set, $\iota:A\to\mathcal D_m$ a multiplicative map ($\iota(ab)=\iota(a)\iota(b)$, not necessarily unital) and $\varphi:A\to\mathcal B(H)$ a surjective monoid homomorphism. Let $b,b'\in A$ with $b$ idempotent and $bb'=b'=b'b$. Let $F\subseteq H$ and $x,y\in F$ satisfy
--   $$
--   \Delta_F\,\varphi(b)\,\Delta_F=\Delta_F,\qquad \Delta_F\,\varphi(b')\,\Delta_F=\Delta_F\cup\{(x,y)\}.
--   $$
--
--   **Theorem.** There are an idempotent $d$ in the corner $bAb$ and a monoid homomorphism $\psi:dAd\to\mathcal B(F)$ such that
--   1. $\psi$ is surjective;
--   2. every permutation $\sigma$ of $F$ lifts to a unit: $\psi(p)=G_\sigma$ for some unit $p$ of $dAd$;
--   3. $\psi(w)=\varphi(w)|_F$ for every $w\in dAd$;
--   4. there is an idempotent $v\in dAd$ with
--   $$
--   \psi(v)=\mathrm{id}_F\cup\{(x,y)\},\qquad \big|\mathrm{Miss}_{\iota(d)}(\iota(v))\big|\le 2\,\big|\mathrm{Miss}_{\iota(b)}(\iota(b'))\big| .
--   $$
--
--   This is the reduction step of the amplification argument. The data $(A,H,\iota,\varphi)$ and the nested pair $b,b'$ are replaced by the finite monoid $dAd$, the label set $F$, the restriction of $\iota$ to $dAd$ (whose value at the identity $d$ is $\iota(d)$) and $\psi$. The new data again consist of a surjective homomorphism with unit lifts and an idempotent representing a single pair. Its cost is at most twice the number of classes lost from $\iota(b)$ to $\iota(b')$, so an induction on the number of labels can be continued on $F$.
--
--   **Formalization Note** Corners are Mathlib's `IsIdempotentElem.Corner` with the monoid structure `cornerMonoid`. The element $d$ lives in the corner monoid of $b$, and $dAd$ is formalized as the corner of $d$ inside that monoid; as a set it equals the corner of $d$ in $A$, and its elements are unwrapped twice (`w.val.val`) to reach $A$. $\mathcal B(F)$ is `RelationMonoid F` for the subtype $F$, and $G_\sigma$ is `(permutationUnit σ).val`. $\mathcal D_m$ is `Diagram m` with fields `forward`, `backward`, `left`, `right` and product `Diagram.comp`; the sign $+$ is `true` and $-$ is `false`. $\mathcal C(e)$ is `e.classes`, a set of pairs in `Bool × Set (Fin m)`, and $\mathrm{Miss}_e(z)$ is `e.missing z`. Cardinalities are `Set.ncard`, which is the true cardinality because these sets are finite. $H$ need not be finite, and $x=y$ is not excluded.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean#L178-L285

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.smaller_relation_instance {A H : Type*} [Monoid A] [Finite A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H) (hφ : Function.Surjective φ)
    (b b' : A) (hb : IsIdempotentElem b) (hbb' : b * b' = b') (hb'b : b' * b = b')
    (F : Set H)
    (hiPi : restrictedIdentity F ○ (φ b).toRel ○ restrictedIdentity F = restrictedIdentity F)
    (x y : F)
    (hpair : restrictedIdentity F ○ (φ b').toRel ○ restrictedIdentity F =
      restrictedIdentity F ∪ {(x.val, y.val)}) :
    ∃ d : hb.Corner, ∃ hd : IsIdempotentElem d, ∃ ψ : hd.Corner →* RelationMonoid F,
      Function.Surjective ψ ∧
      (∀ σ : Equiv.Perm F, ∃ p : hd.Cornerˣ, ψ p = (permutationUnit σ).val) ∧
      (∀ w, (ψ w).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ (φ w.val.val).toRel}) ∧
      ∃ v : hd.Corner, IsIdempotentElem v ∧ (ψ v).toRel = SetRel.id ∪ {(x, y)} ∧
        ((ι d.val).missing (ι v.val.val)).ncard ≤ 2 * ((ι b).missing (ι b')).ncard := by sorry
